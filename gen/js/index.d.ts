// Types for the pcre-vera wrapper. The engine module next door is generated
// and not part of the public surface, so nothing here describes it.
//
// Compilation fixes each pattern's execution path — the lockstep Pike VM
// when eligible, the backtracking matcher otherwise — and match, the limits,
// and the analysis accessors all describe that path. The match configuration
// argument is in its final shape with only the default value active until
// M9; the preallocated match context arrives with the rest of M5.

/** SHA-256 of the TIR artifact the engine was generated from. */
export declare const artifactSha256: string;

/** Compile-time options, with the meanings pcre2 gives them. */
export declare const Flags: {
  readonly CASELESS: number;
  readonly MULTILINE: number;
  readonly DOTALL: number;
  readonly EXTENDED: number;
  readonly UNGREEDY: number;
  readonly ANCHORED: number;
  readonly ENDANCHORED: number;
  readonly DOLLAR_ENDONLY: number;
};

/** What counts as a newline, for the dot, the anchors, and \R under ANYCRLF. */
export declare const Newline: {
  readonly LF: number;
  readonly CR: number;
  readonly CRLF: number;
  readonly ANYCRLF: number;
  readonly ANY: number;
};

/** The convention \R matches under. */
export declare const BSR: {
  readonly UNICODE: number;
  readonly ANYCRLF: number;
};

/** The options one match call adds on top of the pattern's. */
export declare const MatchFlags: {
  readonly NOTBOL: number;
  readonly NOTEOL: number;
  readonly NOTEMPTY: number;
  readonly NOTEMPTY_ATSTART: number;
  readonly ANCHORED: number;
};

/**
 * The one configuration value used consistently across the whole API: match
 * runs under it, the worst-case accessors price it, and the match context of
 * M5 will bake it in. MEMOIZED arrives with M9; until then asking for it is
 * BAD_INPUT.
 */
export declare const MatchConfig: {
  readonly DEFAULT: number;
  readonly MEMOIZED: number;
};

/**
 * What complexityClass answers. LINEAR is a proved claim; NOT_PROVEN_LINEAR
 * is a conservative bound that may overestimate but never underestimate.
 */
export declare const Complexity: {
  readonly NOT_PROVEN_LINEAR: number;
  readonly LINEAR: number;
};

/** Which outcome a PcreError carries. */
export declare const Kind: {
  readonly SYNTAX: "syntax";
  readonly UNSUPPORTED_FEATURE: "unsupportedFeature";
  readonly UNSUPPORTED_OPTION: "unsupportedOption";
  readonly PATTERN_TOO_LARGE: "patternTooLarge";
  readonly RESOURCE_EXCEEDED: "resourceExceeded";
  readonly BAD_INPUT: "badInput";
  readonly INTERNAL: "internal";
  readonly EXCEEDS_BUDGET: "exceedsBudget";
};

export type ErrorKind = (typeof Kind)[keyof typeof Kind];

/**
 * Every way a call can fail. `code` and `offset` are the contract that is
 * tested against pcre2; the message text is ours and may change.
 */
export declare class PcreError extends Error {
  readonly kind: ErrorKind;
  readonly code: number;
  readonly offset: number;
}

/** The largest value each limit may name. A larger one is refused, never clamped. */
export declare const maxCostLimit: number;
export declare const maxMemoryLimit: number;
export declare const maxStackLimit: number;

/**
 * The longest byte sequence either a pattern or a subject may be, since every
 * offset the engine reports has to fit in an i32.
 */
export declare const maxLength: number;

/**
 * The hard budgets one match call runs under: cost in engine cost units,
 * stack in backtrack entries, memory in IR bytes of scratch.
 */
export interface Limits {
  cost: number;
  stack: number;
  memory: number;
}

/** A budget generous enough for ordinary patterns and still finite. */
export declare function defaultLimits(): Limits;

export interface CompileOptions {
  flags?: number;
  newline?: number;
  bsr?: number;
}

export interface MatchOptions {
  start?: number;
  flags?: number;
  limits?: Limits;
  config?: number;
}

/** A compiled pattern. It is immutable, so one may be kept and reused freely. */
export declare class Regexp {
  /** How many capturing groups the pattern has. */
  readonly groupCount: number;

  /** The number of the group with that name, or -1. */
  groupIndex(name: string): number;

  /** Every named group and its number, as a fresh Map. */
  groupNames(): Map<string, number>;

  /**
   * The ovector — byte offsets of the whole match, then a pair per capturing
   * group, with -1 for both ends of a group that did not participate — or
   * null when the subject does not match. Everything else throws a PcreError.
   */
  match(subject: Uint8Array, options?: MatchOptions): Int32Array | null;

  /**
   * The pattern's complexity class, fixed at compilation, as a Complexity
   * value. Takes no configuration because none changes it. Throws a PcreError
   * of kind EXCEEDS_BUDGET when no accepted bound certificate exists.
   */
  complexityClass(): number;

  /**
   * The most a match call on a subject of that length can be charged, in the
   * units limits.cost is stated in, so the number can be passed there
   * unchanged. The bound holds for every subject of that length, every start
   * offset, and every combination of match flags. Throws EXCEEDS_BUDGET for a
   * bound nothing could budget for, BAD_INPUT for a length or configuration
   * outside the documented ranges.
   */
  worstCaseCost(subjectLen: number, config?: number): number;

  /**
   * The deepest the backtrack stack can get on such a call, in the entries
   * limits.stack is stated in.
   */
  worstCaseStackEntries(subjectLen: number, config?: number): number;

  /**
   * The peak scratch reservation of such a call, in the IR bytes
   * limits.memory is stated in.
   */
  worstCaseMemory(subjectLen: number, config?: number): number;
}

/**
 * Compile a pattern, or throw a PcreError saying why not. A string pattern is
 * a convenience that holds only while every code unit is at most 0xff; the
 * canonical form is a Uint8Array. A code unit above that is
 * UNSUPPORTED_FEATURE, since it is asking for the UTF mode of wave 3.
 */
export declare function compile(
  pattern: Uint8Array | string,
  options?: CompileOptions,
): Regexp;
