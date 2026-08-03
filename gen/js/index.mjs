// The JavaScript form of the pcre-vera engine: a thin, hand-written wrapper
// around the module generated from the TIR artifact, giving it the API of
// DESIGN.md section 2.4 with JavaScript conventions.
//
// Compilation fixes each pattern's execution path: the lockstep Pike VM when
// the pattern is eligible — pure stars with consuming bodies, in wave 1 —
// and the backtracking matcher otherwise. match runs that path under the
// caller's hard limits, and the analysis accessors answer for it: complexity
// class and worst-case cost, stack and memory, read off the bound
// certificate compilation stored for the selected path. The match
// configuration argument is in its final shape, though only the default
// value exists — the memoized backtracker is M9, and asking for it early is
// BAD_INPUT, on match and accessors alike. The preallocated match context
// follows.
//
// Patterns and subjects are byte sequences. A pattern may also be a string,
// as a convenience, when every code unit is at most 0xff and can therefore be
// read as one byte; a subject may not, until UTF mode arrives in wave 3.

import {
  Out,
  Usage,
  artifactSha256 as engineArtifactSha256,
  compile as engineCompile,
  match as engineMatch,
  re_class,
  re_cost,
  re_mem,
  re_stack,
  tir_bytes,
  tir_cell,
  tir_zero_vec_u32_512,
} from "./engine.mjs";

/** SHA-256 of the TIR artifact the engine was generated from. */
export const artifactSha256 = engineArtifactSha256;

/** Compile-time options, with the meanings pcre2 gives them. */
export const Flags = Object.freeze({
  CASELESS: 1 << 0,
  MULTILINE: 1 << 1,
  DOTALL: 1 << 2,
  EXTENDED: 1 << 3,
  UNGREEDY: 1 << 4,
  ANCHORED: 1 << 5,
  ENDANCHORED: 1 << 6,
  DOLLAR_ENDONLY: 1 << 7,
});

const KNOWN_FLAGS = Object.values(Flags).reduce((all, bit) => all | bit, 0);

/** What counts as a newline, for the dot, the anchors, and \R under ANYCRLF. */
export const Newline = Object.freeze({
  LF: 0,
  CR: 1,
  CRLF: 2,
  ANYCRLF: 3,
  ANY: 4,
});

/** The convention \R matches under. */
export const BSR = Object.freeze({ UNICODE: 0, ANYCRLF: 1 });

/** The options one match call adds on top of the pattern's. */
export const MatchFlags = Object.freeze({
  NOTBOL: 1 << 0,
  NOTEOL: 1 << 1,
  NOTEMPTY: 1 << 2,
  NOTEMPTY_ATSTART: 1 << 3,
  ANCHORED: 1 << 4,
});

const KNOWN_MATCH_FLAGS = Object.values(MatchFlags).reduce((all, bit) => all | bit, 0);

/**
 * The one configuration value used consistently across the whole API: match
 * runs under it, the worst-case accessors price it, and the match context of
 * M5 will bake it in. It only ever chooses memoized backtracking or not — the
 * Pike/backtracking split is fixed at compilation and is deliberately not a
 * switch a caller can reach. MEMOIZED arrives with M9; until then, and on any
 * pattern not eligible for it after that, asking is BAD_INPUT rather than a
 * silent fallback.
 */
export const MatchConfig = Object.freeze({ DEFAULT: 0, MEMOIZED: 1 });

/**
 * What complexityClass answers. LINEAR is a proved claim — the cost of any
 * match is at most a constant times the subject length plus one — while
 * NOT_PROVEN_LINEAR is the honest remainder: a conservative bound exists,
 * possibly polynomial or exponential in form, and it may overestimate but
 * never underestimate.
 */
export const Complexity = Object.freeze({ NOT_PROVEN_LINEAR: 0, LINEAR: 1 });

/**
 * Which outcome a PcreError carries. SYNTAX is the only one whose code is
 * pcre2's; the others are ours, and DESIGN.md section 2.4 forbids ever
 * repurposing a pcre2 code for them.
 */
export const Kind = Object.freeze({
  SYNTAX: "syntax",
  UNSUPPORTED_FEATURE: "unsupportedFeature",
  UNSUPPORTED_OPTION: "unsupportedOption",
  PATTERN_TOO_LARGE: "patternTooLarge",
  RESOURCE_EXCEEDED: "resourceExceeded",
  BAD_INPUT: "badInput",
  INTERNAL: "internal",
  // The analysis accessors' own refusal, distinct from the runtime
  // RESOURCE_EXCEEDED: no certified bound exists, or the bound is past what
  // any runtime limit could accept, so there is no number here a caller can
  // budget with. It never comes out of match.
  EXCEEDS_BUDGET: "exceedsBudget",
});

/** The largest value each limit may name. A larger one is refused, never clamped. */
export const maxCostLimit = 2 ** 53 - 1;
export const maxMemoryLimit = 2 ** 31 - 1;
export const maxStackLimit = Math.floor((2 ** 31 - 1) / 12);

/**
 * The longest byte sequence either a pattern or a subject may be. Every offset
 * the engine reports is an i32 byte offset, so a longer input could not be
 * described. The engine's own documented pattern limit is far below this; the
 * check exists so that a length the engine's u32 could not hold is refused
 * rather than truncated into an acceptable one.
 */
export const maxLength = 2 ** 31 - 1;

/** A budget generous enough for ordinary patterns and still finite. */
export function defaultLimits() {
  return { cost: 10_000_000, stack: 100_000, memory: 64 * 1024 * 1024 };
}

const CODE_UNSUPPORTED_FEATURE = 1000;
const CODE_UNSUPPORTED_OPTION = 1001;
const CODE_PATTERN_TOO_LARGE = 1002;
const CODE_INTERNAL = 1003;

const STATUS_MATCHED = 0;
const STATUS_OK = 0;
const STATUS_NO_MATCH = 1;
const STATUS_RESOURCE_EXCEEDED = 2;
const STATUS_BAD_INPUT = 3;
const STATUS_EXCEEDS_BUDGET = 4;

const UNSET = 0xffffffff;

// The saturation point of the engine's counter type. A subject length above
// it cannot travel as a counter at all, so it is refused at the door; the
// public maxLength cap below it is the generated code's own BAD_INPUT.
const COUNTER_CAP = 2 ** 53 - 1;

const MESSAGES = {
  [Kind.SYNTAX]: "syntax error",
  [Kind.UNSUPPORTED_FEATURE]: "this release does not support that construct",
  [Kind.UNSUPPORTED_OPTION]: "this release does not support that option",
  [Kind.PATTERN_TOO_LARGE]: "the pattern is past a documented portable limit",
  [Kind.RESOURCE_EXCEEDED]: "the match went over its cost, stack or memory limit",
  [Kind.BAD_INPUT]: "an argument is outside its documented range",
  [Kind.INTERNAL]: "internal error",
  [Kind.EXCEEDS_BUDGET]: "no certified bound fits any runtime limit",
};

/**
 * Every way a call can fail. `code` and `offset` are the contract that is
 * tested against pcre2; the message text is ours and may change.
 */
export class PcreError extends Error {
  constructor(kind, code = 0, offset = 0) {
    let message = `pcre-vera: ${MESSAGES[kind]}`;
    if (kind === Kind.SYNTAX) {
      message += ` ${code} at offset ${offset}`;
    }
    super(message);
    this.name = "PcreError";
    this.kind = kind;
    this.code = code;
    this.offset = offset;
  }
}

function badInput() {
  return new PcreError(Kind.BAD_INPUT);
}

// Anything the engine does not name as one of ours is pcre2's own syntax
// error, which is what the SYNTAX default says.
const KIND_BY_CODE = {
  [CODE_UNSUPPORTED_FEATURE]: Kind.UNSUPPORTED_FEATURE,
  [CODE_UNSUPPORTED_OPTION]: Kind.UNSUPPORTED_OPTION,
  [CODE_PATTERN_TOO_LARGE]: Kind.PATTERN_TOO_LARGE,
  [CODE_INTERNAL]: Kind.INTERNAL,
};

function compileError(code, offset) {
  return new PcreError(KIND_BY_CODE[code] ?? Kind.SYNTAX, code, offset);
}

function whole(value, ceiling) {
  return Number.isInteger(value) && value >= 0 && value <= ceiling;
}

/**
 * An options or limits argument, which has to be something a property can be
 * read off. A parameter default only fires on `undefined`, so `null` would
 * otherwise reach the reads below as a host TypeError rather than as our own
 * BadInput.
 */
function record(value) {
  if (value === null || typeof value !== "object") {
    throw badInput();
  }
  return value;
}

/**
 * The bytes of a pattern. A Uint8Array is the canonical form; a string is a
 * convenience that only works while every code unit fits in a byte, which is
 * as far as Latin-1 goes and as far as this release reads.
 *
 * A code unit above that is not bad input, it is a pattern that wants UTF
 * mode, so it comes back as UNSUPPORTED_FEATURE with the offset of the first
 * code unit that asked for it. A pattern that is neither a string nor bytes is
 * bad input, because there is nothing there to support later.
 */
function patternBytes(pattern) {
  if (pattern instanceof Uint8Array) {
    return pattern;
  }
  if (typeof pattern !== "string") {
    throw badInput();
  }
  const bytes = new Uint8Array(pattern.length);
  for (let i = 0; i < pattern.length; i++) {
    const unit = pattern.charCodeAt(i);
    if (unit > 0xff) {
      throw new PcreError(Kind.UNSUPPORTED_FEATURE, CODE_UNSUPPORTED_FEATURE, i);
    }
    bytes[i] = unit;
  }
  return bytes;
}

function latin1(bytes) {
  let text = "";
  for (let i = 0; i < bytes.length; i++) {
    text += String.fromCharCode(bytes[i]);
  }
  return text;
}

/** A compiled pattern. It is immutable, so one may be kept and reused freely. */
export class Regexp {
  #program;
  #names;

  constructor(program) {
    this.#program = program;
    this.#names = new Map();
    const entries = program.nameents;
    for (let i = 0; i < entries.n; i++) {
      const entry = entries.a[i];
      const name = program.names.a.subarray(entry.off, entry.off + entry.nlen);
      this.#names.set(latin1(name), entry.grp);
    }
    Object.freeze(this);
  }

  /** How many capturing groups the pattern has. */
  get groupCount() {
    return this.#program.ncap;
  }

  /** The number of the group with that name, or -1. */
  groupIndex(name) {
    const number = this.#names.get(name);
    return number === undefined ? -1 : number;
  }

  /** Every named group and its number, as a fresh Map. */
  groupNames() {
    return new Map(this.#names);
  }

  /**
   * Run the pattern against a subject from a byte offset, under hard limits
   * and one match configuration.
   *
   * Returns the ovector — byte offsets of the whole match at entries 0 and 1,
   * then a pair for every capturing group, with -1 for both ends of a group
   * that did not participate — or null when the subject does not match.
   * Everything else throws a PcreError.
   */
  match(subject, options = {}) {
    const {
      start = 0,
      flags = 0,
      limits = defaultLimits(),
      config = MatchConfig.DEFAULT,
    } = record(options);
    if (!(subject instanceof Uint8Array) || subject.length > maxLength) {
      throw badInput();
    }
    if (!whole(flags, KNOWN_MATCH_FLAGS)) {
      throw new PcreError(Kind.UNSUPPORTED_OPTION, CODE_UNSUPPORTED_OPTION);
    }
    // A start offset or a configuration the engine's u32 parameters could not
    // hold is refused here; every other value, offsets past the end of the
    // subject and configurations nobody defined included, is the engine's own
    // BadInput.
    if (!whole(start, 0xffffffff) || !whole(config, 0xffffffff)) {
      throw badInput();
    }
    record(limits);
    if (
      !whole(limits.cost, maxCostLimit) ||
      !whole(limits.stack, maxStackLimit) ||
      !whole(limits.memory, maxMemoryLimit)
    ) {
      throw badInput();
    }
    const ovector = tir_cell(tir_zero_vec_u32_512());
    const usage = tir_cell(new Usage());
    const status = engineMatch(
      this.#program,
      tir_bytes(subject),
      start,
      flags,
      config,
      limits.cost,
      limits.stack,
      limits.memory,
      ovector,
      usage,
    );
    switch (status) {
      case STATUS_MATCHED: {
        const offsets = new Int32Array(ovector.v.n);
        for (let i = 0; i < offsets.length; i++) {
          const slot = ovector.v.a[i];
          offsets[i] = slot === UNSET ? -1 : slot;
        }
        return offsets;
      }
      case STATUS_NO_MATCH:
        return null;
      case STATUS_RESOURCE_EXCEEDED:
        throw new PcreError(Kind.RESOURCE_EXCEEDED);
      case STATUS_BAD_INPUT:
        throw badInput();
      default:
        throw new PcreError(Kind.INTERNAL, status);
    }
  }

  /**
   * The pattern's complexity class, fixed at compilation, as a Complexity
   * value. It takes no configuration because no configuration changes it:
   * memoization alters the constants of an eligible pattern, never the class.
   * A pattern with no accepted bound certificate throws EXCEEDS_BUDGET, since
   * a class claim with no certified bound behind it would be a claim about
   * nothing.
   */
  complexityClass() {
    return answered(re_class(this.#program));
  }

  /**
   * The most a match call on a subject of that length can be charged, in the
   * cost units limits.cost is stated in, so the number can be passed there
   * unchanged. The bound holds for every subject of that length, every start
   * offset, and every combination of match flags. A bound nothing could
   * budget for — no certificate, saturated arithmetic, a number past the
   * limit's own ceiling — throws EXCEEDS_BUDGET.
   */
  worstCaseCost(subjectLen, config = MatchConfig.DEFAULT) {
    return answered(re_cost(this.#program, ...asked(subjectLen, config)));
  }

  /**
   * The deepest the backtrack stack can get on such a call, in the entries
   * limits.stack is stated in.
   */
  worstCaseStackEntries(subjectLen, config = MatchConfig.DEFAULT) {
    return answered(re_stack(this.#program, ...asked(subjectLen, config)));
  }

  /**
   * The peak scratch reservation of such a call, in the IR bytes
   * limits.memory is stated in.
   */
  worstCaseMemory(subjectLen, config = MatchConfig.DEFAULT) {
    return answered(re_mem(this.#program, ...asked(subjectLen, config)));
  }
}

// What the engine's parameters could not hold is refused at the door — a
// fraction, a negative, a boolean, a length past the counter's saturation
// point. Everything representable is the generated code's own decision, so
// the three languages refuse identically.
function asked(subjectLen, config) {
  if (!whole(config, 0xffffffff) || !whole(subjectLen, COUNTER_CAP)) {
    throw badInput();
  }
  return [config, subjectLen];
}

// A generated accessor answer, as JavaScript's shape: the number, or the
// PcreError its status names.
function answered(answer) {
  switch (answer.status) {
    case STATUS_OK:
      return answer.value;
    case STATUS_BAD_INPUT:
      throw badInput();
    case STATUS_EXCEEDS_BUDGET:
      throw new PcreError(Kind.EXCEEDS_BUDGET);
    default:
      throw new PcreError(Kind.INTERNAL, answer.status);
  }
}

/**
 * Compile a pattern, or throw a PcreError saying why not.
 *
 * A syntax error carries pcre2's own code and a byte offset into the pattern.
 * A construct pcre2 accepts and this release does not comes back as
 * UNSUPPORTED_FEATURE rather than as a repurposed pcre2 code, so a caller can
 * always tell "PCRE says this is wrong" from "we do not do this yet".
 */
export function compile(pattern, options = {}) {
  const { flags = 0, newline = Newline.LF, bsr = BSR.UNICODE } = record(options);
  const bytes = patternBytes(pattern);
  if (
    !whole(flags, KNOWN_FLAGS) ||
    !whole(newline, Newline.ANY) ||
    !whole(bsr, BSR.ANYCRLF)
  ) {
    throw new PcreError(Kind.UNSUPPORTED_OPTION, CODE_UNSUPPORTED_OPTION);
  }
  if (bytes.length > maxLength) {
    throw new PcreError(Kind.PATTERN_TOO_LARGE, CODE_PATTERN_TOO_LARGE);
  }
  const out = tir_cell(new Out());
  engineCompile(tir_bytes(bytes), flags, newline, bsr, out);
  if (out.v.err !== 0) {
    throw compileError(out.v.err, out.v.erroff);
  }
  return new Regexp(out.v.re);
}
