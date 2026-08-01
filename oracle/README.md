# The pcre2 oracle

"Correct PCRE" only means something against one exact libpcre2, so this
directory holds that one: `pcre2-pin.toml` names the release, its tarball hash,
the complete configure flags, and everything the linked library must report
back about itself. `pcre2shim/shim.c` is a small C program that links the
pinned library and answers questions about it. The Python side that builds and
drives both lives in `src/pcretruste/oracle/`.

## Building it

```
make oracle          # build if needed
make oracle-verify   # build, then check the result against the pin
```

or, equivalently:

```
uv run python -m pcretruste.oracle build
uv run python -m pcretruste.oracle verify
```

The build downloads the pinned tarball into `tmp/oracle/downloads`, verifies its
SHA-256 before unpacking it, verifies the shipped character tables before
compiling them, configures with the pinned flags, and builds only the 8-bit
library — a couple of seconds, not a minute. Everything lands in a directory
named after a digest of the inputs, described below.

Two environment variables are useful on a build machine:
`PCRETRUSTE_ORACLE_CACHE` moves the cache somewhere shared, and
`PCRETRUSTE_PCRE2_TARBALL` points at a local copy of the tarball for a machine
with no network. The copy is hash-checked exactly like a download.

## What gets checked

A build only counts as the reference if the library agrees, field by field,
with the `[expect]` table of the pin: the release version, Unicode support and
its database version, the newline and `\R` conventions, JIT being absent, the
link size, the parenthesis nesting limit, the compiled widths, and the
character tables. That check runs when the build is made and again every time a
cached build is picked up, along with the recorded hash of the binary itself,
because a directory named after the pin says what was meant to be there, not
what is there now.

One pinned knob is deliberately checked a different way.
`--with-max-varlookbehind=255` changes what compiles and `pcre2_config` has no
field for it, so the corpus pins it by behavior instead: a variable-length
lookbehind branch of 255 must compile and one of 256 must not
(`varlookbehind-at-the-build-limit` and its sibling). Where a build-time knob
can only be seen in behavior, that is where it gets pinned.

The tables deserve a word, since `\w`, `\s`, `\b`, the POSIX classes, and
caseless matching in byte mode are exactly what they decide. They are pinned
twice. Once as a source file: `src/pcre2_chartables.c.dist`, the default C
locale tables the release ships, hashed before it is compiled — the build never
passes `--enable-rebuild-chartables`, which would regenerate them from whatever
locale the build machine happens to have. And once as bytes: the shim recovers
the tables the linked library actually ended up using and reports them, and the
harness hashes those. The recovery uses public functions only: a serialized
pattern carries the tables right after a fixed-size header, and the header size
follows from two sizes the API will tell you (the serialized total, and the
compiled block plus table lengths), so no pcre2 header or internal symbol is
needed. It does lean on that layout, which pcre2 documents as a bytecode dump
rather than a stable format — fair here, because the release is pinned, and the
two independent paths are compared against each other rather than assumed
equal.

## The line protocol

One request per input line, one response per output line, plain ASCII
throughout. The shim keeps running until it reads `quit` or its input ends.

Byte payloads are written `<len>:<hex>` — the decimal byte count, a colon, then
two lowercase hex digits per byte. The redundant length is what makes a line
that got truncated somewhere a parse error instead of a shorter pattern.
Option lists are comma-separated pcre2 option names without their `PCRE2_`
prefix, or `-` for none; an unknown name is an error, never an ignored bit.
Newline and `\R` conventions are single names (`LF`, `CRLF`, `ANYCRLF`, `ANY`,
`CR`, `NUL` and `UNICODE`, `ANYCRLF` respectively), or `-` to leave the
library's own default in place.

```
+---------------------------------------------------------------------------+
| Request                                                                   |
+---------------------------------------------------------------------------+
| hello                                                                     |
| config                                                                    |
| compile <pattern> <options> <newline> <bsr>                               |
| match <pattern> <options> <newline> <bsr> <subject> <start> <matchoptions> |
| quit                                                                      |
+---------------------------------------------------------------------------+

+---------------------------------------------------------------------------+
| Response                                                                  |
+---------------------------------------------------------------------------+
| hello <protocol> <version>          the shim is up                        |
| config <key>=<value> ...            one field per configuration item      |
| compiled <captures> <names> [<number>,<name>]...                          |
| match <pairs> <start> <end> ...     byte offsets, -1 for an unset group   |
| nomatch                                                                   |
| cerror <code> <offset> <message>    compile failed                        |
| merror <code> <message>             match failed (a limit, a bad offset)  |
| error <message>                     the request itself made no sense      |
| bye                                                                       |
+---------------------------------------------------------------------------+
```

The ovector is always reported in full: one pair per capture group plus the
whole match, whatever pcre2's return count was. A group that did not take part
reports `-1 -1`, which is the unset representation DESIGN.md section 2.4 pins
for every language, so pcre2's `PCRE2_UNSET` never leaks out of the harness.

Everything else pcre2 says comes back unchanged, and that is deliberate. The
harness reports what the reference does; it does not translate pcre2's answers
into ours. A start offset past the end of the subject is the clearest case: our
API will answer `BadInput` for it, while pcre2 answers
`PCRE2_ERROR_BADOFFSET`, and the harness reports `merror -33` rather than
pretending the two engines use the same vocabulary. The mapping between them
belongs to the differential comparison, where it can be stated case by case and
where a pcre2 error we did not expect stays distinguishable from one we did.
The pairs the comparison will enforce, once there is an engine to compare
against, are `merror -33` and the UTF-8 error family against our `BadInput`,
and a `cerror` code and offset against the same code and offset from our
compiler.

Match limits are process-wide, given on the command line
(`--match-limit`, `--depth-limit`, `--heap-limit`) and reported in the `config`
response so the harness can check that the pinned values are the ones in force.
They exist to stop a pathological case from wedging the harness, not to mirror
our own budgets: our limits and pcre2's meter different implementation events,
so no setting makes them equivalent. Result comparison is restricted to runs
where our engine finished inside its own budget instead.

## The corpus

`corpus/seed.json` is the hand-written starting corpus: a case names a pattern,
its options, a subject, and what PCRE is supposed to do with it. The
expectations were written from what the constructs mean and then checked
against the pinned build, rather than recorded from a run — a case that
disagrees is either a mistake of ours or a change in pcre2, and both are worth
hearing about. `pytest -k oracle` runs the lot.

## What the build is keyed by

A build lands in a directory named after a digest of the pin, the shim source,
the recipe, and the compiler this machine has. Change any of them and the next
build is a different directory rather than a partly stale one. Picking a cached
build back up is not a matter of trusting that name: the manifest has to
describe this pin, the extracted tree has to still hold the library and the
pinned character table source, the binary has to be the one the manifest
recorded, and the library it links has to still report the pinned
configuration. `make oracle-verify` runs the fuller version, which also checks
the cached tarball's hash, compares the character tables the library uses
against the ones the release ships, and checks the compiler. Neither one
re-verifies the whole extracted tree against the tarball: the tables are the
part of that tree whose contents reach pcre2's observable behavior, and the
rest is covered by the configuration readback and by the build key.
