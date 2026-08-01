/*
 * pcre2shim -- a line-oriented front end to the pinned libpcre2-8 build.
 *
 * The Python harness drives one long-lived process: one request per input
 * line, one response per output line, both plain ASCII. Byte payloads travel
 * as <len>:<hex>, so a pattern or a subject can hold any byte at all, newlines
 * and NULs included, and a truncated line fails to parse instead of quietly
 * turning into a shorter string.
 *
 * The protocol is specified in oracle/README.md. Everything the shim reports
 * about the library it was linked against comes from public pcre2 functions.
 * One of them, recovering the default character tables, also relies on the
 * serialized layout of the pinned 10.47 release, which the pin makes a fixed
 * fact rather than an assumption; see default_tables below.
 *
 * The process deliberately never calls setlocale: a C program starts in the C
 * locale, and the shim never builds locale tables, so every compilation uses
 * the default character tables the pinned release ships with.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PCRE2_CODE_UNIT_WIDTH 8
#include "pcre2.h"

#define SHIM_PROTOCOL 1

static const char *const empty_input = "";

static void die(const char *what)
{
    fprintf(stderr, "pcre2shim: %s\n", what);
    exit(2);
}

/* A growable byte buffer. */

typedef struct {
    uint8_t *data;
    size_t len;
    size_t cap;
} buf;

static void buf_reserve(buf *b, size_t need)
{
    size_t cap;
    uint8_t *grown;

    if (b->cap >= need) return;
    cap = (b->cap != 0) ? b->cap : 64;
    while (cap < need) {
        if (cap > (size_t)-1 / 2) die("buffer too large");
        cap *= 2;
    }
    grown = realloc(b->data, cap);
    if (grown == NULL) die("out of memory");
    b->data = grown;
    b->cap = cap;
}

/*
 * Read one line with its ending removed, or NULL at end of input. The buffer
 * lives across calls, so a long fuzzing run settles into no allocation at all.
 */
static char *line_buffer;
static size_t line_capacity;

static char *read_line(void)
{
    ssize_t length = getline(&line_buffer, &line_capacity, stdin);

    if (length < 0) return NULL;
    while (length > 0 && (line_buffer[length - 1] == '\n' ||
                          line_buffer[length - 1] == '\r')) {
        line_buffer[--length] = '\0';
    }
    return line_buffer;
}

/* Whitespace-separated tokens, cut out of the line in place. */

typedef struct {
    char *rest;
} tokens;

static char *next_token(tokens *t)
{
    char *start;

    while (*t->rest == ' ' || *t->rest == '\t') t->rest++;
    if (*t->rest == '\0') return NULL;
    start = t->rest;
    while (*t->rest != '\0' && *t->rest != ' ' && *t->rest != '\t') t->rest++;
    if (*t->rest != '\0') *t->rest++ = '\0';
    return start;
}

/*
 * A strictly decimal unsigned value: digits only, so no sign slips through as a
 * huge positive number, no overflow, and the exact terminator the caller
 * expects. Returns 0 on anything else.
 */
static int parse_uint(const char *token, char terminator, unsigned long long limit,
                      unsigned long long *out)
{
    char *end;
    unsigned long long value;

    if (token == NULL || token[0] < '0' || token[0] > '9') return 0;
    errno = 0;
    value = strtoull(token, &end, 10);
    if (end == token || *end != terminator || errno == ERANGE) return 0;
    if (value > limit) return 0;
    *out = value;
    return 1;
}

static int hex_value(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/*
 * Decode a <len>:<hex> payload. Returns 0 if the token is malformed, which
 * includes a count that does not fit a size_t or that would overflow the
 * arithmetic below: the length is there to catch a damaged line, so it has to
 * be checked rather than merely used.
 */
static int decode_blob(const char *token, buf *out)
{
    unsigned long long count;
    size_t length;
    const char *hex;
    size_t i;

    if (!parse_uint(token, ':', ((size_t)-1 - 1) / 2, &count)) return 0;
    length = (size_t)count;

    hex = strchr(token, ':') + 1;
    if (strlen(hex) != length * 2) return 0;

    buf_reserve(out, length + 1);
    for (i = 0; i < length; i++) {
        int hi = hex_value(hex[2 * i]);
        int lo = hex_value(hex[2 * i + 1]);
        if (hi < 0 || lo < 0) return 0;
        out->data[i] = (uint8_t)((hi << 4) | lo);
    }
    out->len = length;
    return 1;
}

static void print_blob(const uint8_t *data, size_t len)
{
    static const char digits[] = "0123456789abcdef";
    size_t i;

    printf("%zu:", len);
    for (i = 0; i < len; i++) {
        putchar_unlocked(digits[data[i] >> 4]);
        putchar_unlocked(digits[data[i] & 0x0f]);
    }
}

/* Option names, without their PCRE2_ prefix. */

typedef struct {
    const char *name;
    uint32_t bit;
} option_entry;

static const option_entry compile_options[] = {
    { "ALLOW_EMPTY_CLASS", PCRE2_ALLOW_EMPTY_CLASS },
    { "ALT_BSUX", PCRE2_ALT_BSUX },
    { "ALT_CIRCUMFLEX", PCRE2_ALT_CIRCUMFLEX },
    { "ALT_VERBNAMES", PCRE2_ALT_VERBNAMES },
    { "ANCHORED", PCRE2_ANCHORED },
    { "AUTO_CALLOUT", PCRE2_AUTO_CALLOUT },
    { "CASELESS", PCRE2_CASELESS },
    { "DOLLAR_ENDONLY", PCRE2_DOLLAR_ENDONLY },
    { "DOTALL", PCRE2_DOTALL },
    { "DUPNAMES", PCRE2_DUPNAMES },
    { "ENDANCHORED", PCRE2_ENDANCHORED },
    { "EXTENDED", PCRE2_EXTENDED },
    { "EXTENDED_MORE", PCRE2_EXTENDED_MORE },
    { "FIRSTLINE", PCRE2_FIRSTLINE },
    { "LITERAL", PCRE2_LITERAL },
    { "MATCH_UNSET_BACKREF", PCRE2_MATCH_UNSET_BACKREF },
    { "MULTILINE", PCRE2_MULTILINE },
    { "NEVER_BACKSLASH_C", PCRE2_NEVER_BACKSLASH_C },
    { "NEVER_UCP", PCRE2_NEVER_UCP },
    { "NEVER_UTF", PCRE2_NEVER_UTF },
    { "NO_AUTO_CAPTURE", PCRE2_NO_AUTO_CAPTURE },
    { "NO_AUTO_POSSESS", PCRE2_NO_AUTO_POSSESS },
    { "NO_DOTSTAR_ANCHOR", PCRE2_NO_DOTSTAR_ANCHOR },
    { "NO_START_OPTIMIZE", PCRE2_NO_START_OPTIMIZE },
    { "NO_UTF_CHECK", PCRE2_NO_UTF_CHECK },
    { "UCP", PCRE2_UCP },
    { "UNGREEDY", PCRE2_UNGREEDY },
    { "USE_OFFSET_LIMIT", PCRE2_USE_OFFSET_LIMIT },
    { "UTF", PCRE2_UTF },
    { NULL, 0 }
};

static const option_entry match_options[] = {
    { "ANCHORED", PCRE2_ANCHORED },
    { "ENDANCHORED", PCRE2_ENDANCHORED },
    { "NOTBOL", PCRE2_NOTBOL },
    { "NOTEMPTY", PCRE2_NOTEMPTY },
    { "NOTEMPTY_ATSTART", PCRE2_NOTEMPTY_ATSTART },
    { "NOTEOL", PCRE2_NOTEOL },
    { "NO_JIT", PCRE2_NO_JIT },
    { "NO_UTF_CHECK", PCRE2_NO_UTF_CHECK },
    { NULL, 0 }
};

static const option_entry newline_names[] = {
    { "ANY", PCRE2_NEWLINE_ANY },
    { "ANYCRLF", PCRE2_NEWLINE_ANYCRLF },
    { "CR", PCRE2_NEWLINE_CR },
    { "CRLF", PCRE2_NEWLINE_CRLF },
    { "LF", PCRE2_NEWLINE_LF },
    { "NUL", PCRE2_NEWLINE_NUL },
    { NULL, 0 }
};

static const option_entry bsr_names[] = {
    { "ANYCRLF", PCRE2_BSR_ANYCRLF },
    { "UNICODE", PCRE2_BSR_UNICODE },
    { NULL, 0 }
};

static int lookup_option(const option_entry *table, const char *name, size_t len,
                         uint32_t *out)
{
    const option_entry *e;

    for (e = table; e->name != NULL; e++) {
        if (strlen(e->name) == len && memcmp(e->name, name, len) == 0) {
            *out = e->bit;
            return 1;
        }
    }
    return 0;
}

/*
 * Parse a comma-separated option list, or "-" for none. Returns 0 on an
 * unknown name, which is a protocol error rather than a silently ignored bit.
 */
static int parse_option_list(const char *token, const option_entry *table,
                             uint32_t *out)
{
    const char *p = token;

    *out = 0;
    if (token == NULL) return 0;
    if (strcmp(token, "-") == 0) return 1;

    for (;;) {
        const char *comma = strchr(p, ',');
        size_t len = (comma != NULL) ? (size_t)(comma - p) : strlen(p);
        uint32_t bit;

        if (len == 0) return 0;
        if (!lookup_option(table, p, len, &bit)) return 0;
        *out |= bit;
        if (comma == NULL) break;
        p = comma + 1;
    }
    return 1;
}

/*
 * Parse a single symbolic value, or "-" for zero, which every convention table
 * here reads as "leave the library default alone": PCRE2_NEWLINE_* starts at 1
 * and so does PCRE2_BSR_*.
 */
static int parse_convention(const char *token, const option_entry *table,
                            uint32_t *out)
{
    if (token == NULL) return 0;
    if (strcmp(token, "-") == 0) {
        *out = 0;
        return 1;
    }
    return lookup_option(table, token, strlen(token), out);
}

static void respond_error(const char *message)
{
    printf("error ");
    print_blob((const uint8_t *)message, strlen(message));
    putchar('\n');
}

static void print_error_message(int code)
{
    PCRE2_UCHAR message[256];
    int len = pcre2_get_error_message(code, message, sizeof(message));

    print_blob((const uint8_t *)message, (len > 0) ? (size_t)len : 0);
    putchar('\n');
}

static void respond_compile_error(int code, PCRE2_SIZE offset)
{
    printf("cerror %d %llu ", code, (unsigned long long)offset);
    print_error_message(code);
}

static void respond_match_error(int code)
{
    printf("merror %d ", code);
    print_error_message(code);
}

/* Limits applied to every match, or 0 for "leave the library default". */

typedef struct {
    uint32_t match_limit;
    uint32_t depth_limit;
    uint32_t heap_limit_kib;
} shim_limits;

static shim_limits limits;
static pcre2_match_context *match_context;

/*
 * Compile with the requested options and conventions. On failure the response
 * has already been written.
 */
static pcre2_code *compile_pattern(const buf *pattern, uint32_t options,
                                   uint32_t newline, uint32_t bsr)
{
    pcre2_compile_context *ccontext = NULL;
    pcre2_code *code;
    int error_code;
    PCRE2_SIZE error_offset;
    const uint8_t *bytes = (pattern->len != 0) ? pattern->data
                                               : (const uint8_t *)empty_input;

    if (newline != 0 || bsr != 0) {
        ccontext = pcre2_compile_context_create(NULL);
        if (ccontext == NULL) die("out of memory");
        if (newline != 0) pcre2_set_newline(ccontext, newline);
        if (bsr != 0) pcre2_set_bsr(ccontext, bsr);
    }

    code = pcre2_compile((PCRE2_SPTR)bytes, pattern->len, options,
                         &error_code, &error_offset, ccontext);
    if (ccontext != NULL) pcre2_compile_context_free(ccontext);
    if (code == NULL) respond_compile_error(error_code, error_offset);
    return code;
}

static void handle_compile(pcre2_code *code)
{
    uint32_t capture_count = 0;
    uint32_t name_count = 0;
    uint32_t entry_size = 0;
    PCRE2_SPTR name_table = NULL;
    uint32_t i;

    pcre2_pattern_info(code, PCRE2_INFO_CAPTURECOUNT, &capture_count);
    pcre2_pattern_info(code, PCRE2_INFO_NAMECOUNT, &name_count);
    if (name_count > 0) {
        pcre2_pattern_info(code, PCRE2_INFO_NAMEENTRYSIZE, &entry_size);
        pcre2_pattern_info(code, PCRE2_INFO_NAMETABLE, &name_table);
    }

    printf("compiled %u %u", capture_count, name_count);
    for (i = 0; i < name_count; i++) {
        PCRE2_SPTR entry = name_table + (size_t)i * entry_size;
        unsigned group = ((unsigned)entry[0] << 8) | (unsigned)entry[1];
        const uint8_t *name = (const uint8_t *)(entry + 2);

        printf(" %u,", group);
        print_blob(name, strlen((const char *)name));
    }
    putchar('\n');
}

static void handle_match(pcre2_code *code, const buf *subject,
                         PCRE2_SIZE start_offset, uint32_t options)
{
    uint32_t capture_count = 0;
    pcre2_match_data *match_data;
    PCRE2_SIZE *ovector;
    const uint8_t *bytes = (subject->len != 0) ? subject->data
                                               : (const uint8_t *)empty_input;
    int rc;
    uint32_t i;

    pcre2_pattern_info(code, PCRE2_INFO_CAPTURECOUNT, &capture_count);
    match_data = pcre2_match_data_create(capture_count + 1, NULL);
    if (match_data == NULL) die("out of memory");

    rc = pcre2_match(code, (PCRE2_SPTR)bytes, subject->len, start_offset,
                     options, match_data, match_context);

    if (rc == PCRE2_ERROR_NOMATCH) {
        printf("nomatch\n");
    } else if (rc < 0) {
        respond_match_error(rc);
    } else if (rc == 0) {
        /* Cannot happen: the ovector is sized from the capture count. */
        respond_error("ovector too small");
    } else {
        ovector = pcre2_get_ovector_pointer(match_data);
        printf("match %u", capture_count + 1);
        for (i = 0; i <= capture_count; i++) {
            /*
             * Pairs at or above rc were never set by this match, and a set
             * pair can still be PCRE2_UNSET for a group that did not take
             * part. Both are the unset representation the design pins: -1.
             */
            if (i >= (uint32_t)rc || ovector[2 * i] == PCRE2_UNSET ||
                ovector[2 * i + 1] == PCRE2_UNSET) {
                printf(" -1 -1");
            } else {
                printf(" %llu %llu", (unsigned long long)ovector[2 * i],
                       (unsigned long long)ovector[2 * i + 1]);
            }
        }
        putchar('\n');
    }

    pcre2_match_data_free(match_data);
}

/*
 * The default character tables of the linked library. A serialized pattern
 * carries them right after a fixed-size header, and the header size follows
 * from two sizes the public API will tell us, so no pcre2 header or internal
 * symbol is needed. It does depend on that layout, which pcre2 documents as a
 * bytecode dump rather than a stable format: fine here, because the release is
 * pinned, and checked, because the Python side compares the bytes this returns
 * against the ones parsed out of the release's own pcre2_chartables.c.dist.
 */
static int default_tables(buf *out)
{
    pcre2_code *code;
    int error_code;
    PCRE2_SIZE error_offset;
    PCRE2_SIZE block_size = 0;
    uint32_t tables_length = 0;
    uint8_t *bytes = NULL;
    PCRE2_SIZE byte_count = 0;
    size_t header;
    int32_t rc;

    code = pcre2_compile((PCRE2_SPTR)"a", 1, 0, &error_code, &error_offset, NULL);
    if (code == NULL) return 0;

    if (pcre2_pattern_info(code, PCRE2_INFO_SIZE, &block_size) != 0 ||
        pcre2_config(PCRE2_CONFIG_TABLES_LENGTH, &tables_length) < 0) {
        pcre2_code_free(code);
        return 0;
    }

    rc = pcre2_serialize_encode((const pcre2_code **)&code, 1, &bytes,
                                &byte_count, NULL);
    pcre2_code_free(code);
    if (rc < 0) return 0;

    if (byte_count < (PCRE2_SIZE)tables_length + block_size) {
        pcre2_serialize_free(bytes);
        return 0;
    }
    header = (size_t)(byte_count - tables_length - block_size);

    buf_reserve(out, tables_length + 1);
    memcpy(out->data, bytes + header, tables_length);
    out->len = tables_length;
    pcre2_serialize_free(bytes);
    return 1;
}

static void print_config_uint(const char *key, uint32_t what)
{
    uint32_t value = 0;

    if (pcre2_config(what, &value) < 0) die("pcre2_config failed");
    printf(" %s=%u", key, value);
}

/*
 * pcre2_config takes no buffer size, so ask for the length first. The reported
 * length counts the terminating NUL, which the returned length here does not.
 */
static size_t config_string(uint32_t what, char *value, size_t size)
{
    int needed = pcre2_config(what, NULL);

    if (needed <= 0 || (size_t)needed > size) die("pcre2_config failed");
    if (pcre2_config(what, value) != needed) die("pcre2_config failed");
    return (size_t)needed - 1;
}

static void print_config_string(const char *key, uint32_t what)
{
    char value[128];
    size_t len = config_string(what, value, sizeof(value));

    printf(" %s=", key);
    print_blob((const uint8_t *)value, len);
}

static int has_trailing_tokens(tokens *t)
{
    if (next_token(t) == NULL) return 0;
    respond_error("trailing tokens");
    return 1;
}

static void handle_hello(void)
{
    char version[128];
    size_t len = config_string(PCRE2_CONFIG_VERSION, version, sizeof(version));

    printf("hello %d ", SHIM_PROTOCOL);
    print_blob((const uint8_t *)version, len);
    putchar('\n');
}

static void handle_config(void)
{
    buf tables = { NULL, 0, 0 };

    printf("config protocol=%d", SHIM_PROTOCOL);
    print_config_string("version", PCRE2_CONFIG_VERSION);
    print_config_uint("unicode", PCRE2_CONFIG_UNICODE);
    print_config_string("unicode_version", PCRE2_CONFIG_UNICODE_VERSION);
    print_config_uint("newline", PCRE2_CONFIG_NEWLINE);
    print_config_uint("bsr", PCRE2_CONFIG_BSR);
    print_config_uint("jit", PCRE2_CONFIG_JIT);
    print_config_uint("link_size", PCRE2_CONFIG_LINKSIZE);
    print_config_uint("effective_link_size", PCRE2_CONFIG_EFFECTIVE_LINKSIZE);
    print_config_uint("parens_nest_limit", PCRE2_CONFIG_PARENSLIMIT);
    print_config_uint("match_limit", PCRE2_CONFIG_MATCHLIMIT);
    print_config_uint("depth_limit", PCRE2_CONFIG_DEPTHLIMIT);
    print_config_uint("heap_limit", PCRE2_CONFIG_HEAPLIMIT);
    print_config_uint("never_backslash_c", PCRE2_CONFIG_NEVER_BACKSLASH_C);
    print_config_uint("compiled_widths", PCRE2_CONFIG_COMPILED_WIDTHS);
    print_config_uint("tables_length", PCRE2_CONFIG_TABLES_LENGTH);
    printf(" applied_match_limit=%u", limits.match_limit);
    printf(" applied_depth_limit=%u", limits.depth_limit);
    printf(" applied_heap_limit=%u", limits.heap_limit_kib);

    if (!default_tables(&tables)) die("could not read the default tables");
    printf(" tables=");
    print_blob(tables.data, tables.len);
    free(tables.data);
    putchar('\n');
}

static PCRE2_SIZE parse_offset(const char *token, int *ok)
{
    unsigned long long value;

    *ok = parse_uint(token, '\0', (unsigned long long)(PCRE2_SIZE)-1, &value);
    return *ok ? (PCRE2_SIZE)value : 0;
}

static void handle_request(char *line)
{
    static buf pattern = { NULL, 0, 0 };
    static buf subject = { NULL, 0, 0 };
    tokens t;
    const char *command;

    t.rest = line;
    command = next_token(&t);
    if (command == NULL) {
        /* One line in, one line out, so an empty line still gets an answer. */
        respond_error("empty request");
        return;
    }

    if (strcmp(command, "hello") == 0) {
        if (!has_trailing_tokens(&t)) handle_hello();
        return;
    }

    if (strcmp(command, "config") == 0) {
        if (!has_trailing_tokens(&t)) handle_config();
        return;
    }

    if (strcmp(command, "compile") == 0 || strcmp(command, "match") == 0) {
        int matching = (strcmp(command, "match") == 0);
        uint32_t compile_flags = 0;
        uint32_t match_flags = 0;
        uint32_t newline = 0;
        uint32_t bsr = 0;
        PCRE2_SIZE start_offset = 0;
        pcre2_code *code;
        int ok;

        if (!decode_blob(next_token(&t), &pattern)) {
            respond_error("bad pattern payload");
            return;
        }
        if (!parse_option_list(next_token(&t), compile_options, &compile_flags)) {
            respond_error("bad compile options");
            return;
        }
        if (!parse_convention(next_token(&t), newline_names, &newline)) {
            respond_error("bad newline convention");
            return;
        }
        if (!parse_convention(next_token(&t), bsr_names, &bsr)) {
            respond_error("bad bsr convention");
            return;
        }
        if (matching) {
            if (!decode_blob(next_token(&t), &subject)) {
                respond_error("bad subject payload");
                return;
            }
            start_offset = parse_offset(next_token(&t), &ok);
            if (!ok) {
                respond_error("bad start offset");
                return;
            }
            if (!parse_option_list(next_token(&t), match_options, &match_flags)) {
                respond_error("bad match options");
                return;
            }
        }
        if (has_trailing_tokens(&t)) return;

        code = compile_pattern(&pattern, compile_flags, newline, bsr);
        if (code == NULL) return;

        if (matching) {
            handle_match(code, &subject, start_offset, match_flags);
        } else {
            handle_compile(code);
        }
        pcre2_code_free(code);
        return;
    }

    respond_error("unknown command");
}

static int parse_limit_argument(const char *arg, const char *name, uint32_t *out)
{
    size_t len = strlen(name);
    unsigned long long value;

    if (strncmp(arg, name, len) != 0 || arg[len] != '=') return 0;
    if (!parse_uint(arg + len + 1, '\0', 0xffffffffULL, &value)) {
        die("bad limit argument");
    }
    *out = (uint32_t)value;
    return 1;
}

int main(int argc, char **argv)
{
    char *line;
    int i;

    for (i = 1; i < argc; i++) {
        if (parse_limit_argument(argv[i], "--match-limit", &limits.match_limit)) continue;
        if (parse_limit_argument(argv[i], "--depth-limit", &limits.depth_limit)) continue;
        if (parse_limit_argument(argv[i], "--heap-limit", &limits.heap_limit_kib)) continue;
        die("unknown argument");
    }

    match_context = pcre2_match_context_create(NULL);
    if (match_context == NULL) die("out of memory");
    if (limits.match_limit != 0) {
        pcre2_set_match_limit(match_context, limits.match_limit);
    }
    if (limits.depth_limit != 0) {
        pcre2_set_depth_limit(match_context, limits.depth_limit);
    }
    if (limits.heap_limit_kib != 0) {
        pcre2_set_heap_limit(match_context, limits.heap_limit_kib);
    }

    while ((line = read_line()) != NULL) {
        if (strcmp(line, "quit") == 0) {
            printf("bye\n");
            break;
        }
        handle_request(line);
        if (fflush(stdout) != 0) die("write failed");
    }

    if (fflush(stdout) != 0) die("write failed");
    free(line_buffer);
    pcre2_match_context_free(match_context);
    return 0;
}
