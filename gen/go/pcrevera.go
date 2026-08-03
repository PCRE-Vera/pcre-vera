// Package pcrevera is the Go form of the pcre-vera engine: a thin,
// hand-written wrapper around the code generated from the TIR artifact, giving
// it the API of DESIGN.md section 2.4 with Go conventions.
//
// Compilation fixes each pattern's execution path: the lockstep Pike VM when
// the pattern is eligible — pure stars with consuming bodies, in wave 1 —
// and the backtracking matcher otherwise. Match runs that path under the
// caller's hard limits, and the analysis accessors answer for it: complexity
// class and worst-case cost, stack and memory, read off the bound
// certificate compilation stored for the selected path. The match
// configuration argument is in its final shape, though only the default
// value exists — the memoized backtracker is M9, and asking for it early is
// BadInput, on Match and accessors alike. The preallocated match context
// follows.
//
// A compiled pattern is immutable, so one may be shared across goroutines; a
// match call keeps all of its state on its own stack and in scratch it
// allocates itself.
//
// The subject is a byte sequence and stays one: string conveniences arrive
// with UTF mode in wave 3. The pattern is a Go string because a Go string
// already is an arbitrary byte sequence.
package pcrevera

import (
	"maps"
	"strconv"

	"github.com/PCRE-Vera/pcre-vera/gen/go/internal/engine"
)

// ArtifactSHA256 is the SHA-256 of the TIR artifact the engine was generated
// from. It identifies the exact program this package runs.
const ArtifactSHA256 = engine.ArtifactSHA256

// Flags are the compile-time options, with the meanings pcre2 gives them.
type Flags uint32

const (
	Caseless      Flags = 1 << 0
	Multiline     Flags = 1 << 1
	DotAll        Flags = 1 << 2
	Extended      Flags = 1 << 3
	Ungreedy      Flags = 1 << 4
	Anchored      Flags = 1 << 5
	EndAnchored   Flags = 1 << 6
	DollarEndOnly Flags = 1 << 7
)

const knownFlags = Caseless | Multiline | DotAll | Extended | Ungreedy |
	Anchored | EndAnchored | DollarEndOnly

// Newline is the convention that decides what a newline is, for the dot, the
// anchors, and \R under BSRAnyCRLF. The zero value is a bare line feed.
type Newline uint32

const (
	NewlineLF Newline = iota
	NewlineCR
	NewlineCRLF
	NewlineAnyCRLF
	NewlineAny
)

// BSR is the convention \R matches under. The zero value is the Unicode one,
// which is what the pinned pcre2 is built with.
type BSR uint32

const (
	BSRUnicode BSR = iota
	BSRAnyCRLF
)

// Options is everything a pattern is compiled against.
type Options struct {
	Flags   Flags
	Newline Newline
	BSR     BSR
}

// MatchFlags are the options one match call adds on top of the pattern's.
type MatchFlags uint32

const (
	NotBOL MatchFlags = 1 << 0
	NotEOL MatchFlags = 1 << 1
	// NotEmpty refuses an empty match anywhere; NotEmptyAtStart refuses one
	// only at the offset the attempt started from.
	NotEmpty        MatchFlags = 1 << 2
	NotEmptyAtStart MatchFlags = 1 << 3
	MatchAnchored   MatchFlags = 1 << 4
)

const knownMatchFlags = NotBOL | NotEOL | NotEmpty | NotEmptyAtStart | MatchAnchored

// MatchConfig is the one configuration value used consistently across the
// whole API: Match runs under it, the worst-case accessors price it, and the
// match context of M5 will bake it in. It only ever chooses memoized
// backtracking or not — the Pike/backtracking split is fixed at compilation
// and is deliberately not a switch a caller can reach.
//
// The underlying type is wider than the engine's u32 parameter on purpose,
// like the start offset's: a value past the u32 range stays representable and
// is refused as BadInput, rather than a caller's conversion silently wrapping
// it into a valid one.
type MatchConfig uint64

const (
	// DefaultConfig is the execution path compilation selected for the
	// pattern, which is the right choice unless a caller knows better.
	DefaultConfig MatchConfig = 0
	// Memoized asks for the memoized backtracker. It arrives with M9; until
	// then, and on any pattern not eligible for it after that, asking is
	// BadInput rather than a silent fallback.
	Memoized MatchConfig = 1
)

// Limits are the hard budgets one match call runs under: cost in engine cost
// units, stack in backtrack entries, memory in IR bytes of scratch. Those are
// the units the analyzer states its bounds in, so a bound it reports can be
// passed here unchanged.
type Limits struct {
	Cost   uint64
	Stack  uint32
	Memory uint64
}

// The largest value each limit may name. A larger one is refused rather than
// clamped, so enforcement is identical in every language: cost saturates at
// the counter cap, memory at the portable allocation ceiling, and stack at
// that ceiling divided by what one backtrack entry weighs.
const (
	MaxCostLimit   uint64 = 1<<53 - 1
	MaxMemoryLimit uint64 = 1<<31 - 1
	MaxStackLimit  uint32 = (1<<31 - 1) / 12
)

// MaxLength is the longest byte sequence either a pattern or a subject may be.
// Every offset the engine reports is an i32 byte offset, so a longer input
// could not be described (DESIGN.md section 2.4). The engine's own documented
// pattern limit is far below this; the check exists so that a length the
// engine's u32 could not hold is refused rather than truncated into an
// acceptable one.
const MaxLength = 1<<31 - 1

// DefaultLimits is a budget generous enough for ordinary patterns and still
// finite, in the spirit of pcre2's match_limit.
func DefaultLimits() Limits {
	return Limits{Cost: 10_000_000, Stack: 100_000, Memory: 64 << 20}
}

// Kind says which outcome an Error carries. Syntax is the only one whose Code
// is pcre2's; the others are ours, and DESIGN.md section 2.4 forbids ever
// repurposing a pcre2 code for them.
type Kind int

const (
	Syntax Kind = iota + 1
	UnsupportedFeature
	UnsupportedOption
	PatternTooLarge
	ResourceExceeded
	BadInput
	Internal
	// ExceedsBudget is the analysis accessors' own refusal, distinct from the
	// runtime ResourceExceeded: no certified bound exists, or the bound is
	// past what any runtime limit could accept, so there is no number here a
	// caller can budget with. It never comes out of Match.
	ExceedsBudget
)

// Error is every way a call can fail. Code and Offset are the contract that is
// tested against pcre2; the message text is ours and may change.
type Error struct {
	Kind   Kind
	Code   int
	Offset int
}

func (e *Error) Error() string {
	switch e.Kind {
	case Syntax:
		return "pcre-vera: syntax error " + strconv.Itoa(e.Code) +
			" at offset " + strconv.Itoa(e.Offset)
	case UnsupportedFeature:
		return "pcre-vera: this release does not support that construct, at offset " +
			strconv.Itoa(e.Offset)
	case UnsupportedOption:
		return "pcre-vera: this release does not support that option"
	case PatternTooLarge:
		return "pcre-vera: the pattern is past a documented portable limit"
	case ResourceExceeded:
		return "pcre-vera: the match went over its cost, stack or memory limit"
	case BadInput:
		return "pcre-vera: an argument is outside its documented range"
	case ExceedsBudget:
		return "pcre-vera: no certified bound fits any runtime limit"
	}
	return "pcre-vera: internal error " + strconv.Itoa(e.Code)
}

// The engine's own error codes, above the range pcre2 uses, and its match
// outcomes. They are the calling convention of the generated program rather
// than anything a caller ever passes in.
const (
	codeUnsupportedFeature = 1000
	codeUnsupportedOption  = 1001
	codePatternTooLarge    = 1002
	codeInternal           = 1003

	statusMatched          = 0
	statusOK               = 0
	statusNoMatch          = 1
	statusResourceExceeded = 2
	statusBadInput         = 3
	statusExceedsBudget    = 4

	unset = 0xFFFFFFFF
)

// The saturation point of the engine's counter type. A subject length above
// it cannot travel as a counter at all, so it is refused at the door; the
// public MaxLength cap below it is the generated code's own BadInput.
const counterCap uint64 = 1<<53 - 1

// Regexp is a compiled pattern. It is immutable, so one may be shared freely.
type Regexp struct {
	program engine.Re
	groups  int
	names   map[string]int
}

// Compile turns a pattern into a Regexp, or says why it will not.
//
// The pattern is a byte sequence and the offset in a syntax error is a byte
// offset into it. A construct pcre2 accepts and this release does not comes
// back as UnsupportedFeature rather than as a repurposed pcre2 code, so a
// caller can always tell "PCRE says this is wrong" from "we do not do this
// yet".
func Compile(pattern string, opts Options) (*Regexp, error) {
	if opts.Flags&^knownFlags != 0 || opts.Newline > NewlineAny || opts.BSR > BSRAnyCRLF {
		return nil, &Error{Kind: UnsupportedOption, Code: codeUnsupportedOption}
	}
	if len(pattern) > MaxLength {
		return nil, &Error{Kind: PatternTooLarge, Code: codePatternTooLarge}
	}
	var out engine.Out
	engine.Tir_compile(
		[]byte(pattern),
		uint32(opts.Flags),
		uint32(opts.Newline),
		uint32(opts.BSR),
		&out,
	)
	if code := out.Tir_err(); code != 0 {
		return nil, compileError(int(code), int(out.Tir_erroff()))
	}
	program := out.Tir_re()
	return &Regexp{
		program: program,
		groups:  int(program.Tir_ncap()),
		names:   groupNames(&program),
	}, nil
}

// MustCompile is Compile for a pattern that is known good at authoring time.
func MustCompile(pattern string, opts Options) *Regexp {
	re, err := Compile(pattern, opts)
	if err != nil {
		panic(err)
	}
	return re
}

func compileError(code int, offset int) error {
	switch code {
	case codeUnsupportedFeature:
		return &Error{Kind: UnsupportedFeature, Code: code, Offset: offset}
	case codeUnsupportedOption:
		return &Error{Kind: UnsupportedOption, Code: code, Offset: offset}
	case codePatternTooLarge:
		return &Error{Kind: PatternTooLarge, Code: code, Offset: offset}
	case codeInternal:
		return &Error{Kind: Internal, Code: code, Offset: offset}
	}
	return &Error{Kind: Syntax, Code: code, Offset: offset}
}

func groupNames(program *engine.Re) map[string]int {
	entries := program.Tir_nameents()
	if len(entries) == 0 {
		return nil
	}
	blob := program.Tir_names()
	names := make(map[string]int, len(entries))
	for i := range entries {
		at := int(entries[i].Tir_off())
		names[string(blob[at:at+int(entries[i].Tir_nlen())])] = int(entries[i].Tir_grp())
	}
	return names
}

// NumSubexp is how many capturing groups the pattern has.
func (re *Regexp) NumSubexp() int { return re.groups }

// SubexpIndex is the number of the group with that name, or -1.
func (re *Regexp) SubexpIndex(name string) int {
	if number, ok := re.names[name]; ok {
		return number
	}
	return -1
}

// SubexpNames maps every named group to its number. The map is a copy, so a
// caller may keep it without reaching into the compiled pattern.
func (re *Regexp) SubexpNames() map[string]int {
	return maps.Clone(re.names)
}

// Match runs the pattern against a subject from a byte offset, under hard
// limits and one match configuration, and returns the ovector: byte offsets
// of the whole match at entries 0 and 1, then a pair for every capturing
// group. A group that did not participate reports -1 for both ends.
//
// A subject that does not match is a nil ovector and a nil error. Everything
// else — a budget exhausted, a start offset outside the subject, a limit past
// what any target could honor, a configuration the pattern cannot run under —
// is an *Error.
func (re *Regexp) Match(
	subject []byte,
	start int,
	flags MatchFlags,
	limits Limits,
	config MatchConfig,
) ([]int32, error) {
	if flags&^knownMatchFlags != 0 {
		return nil, &Error{Kind: UnsupportedOption, Code: codeUnsupportedOption}
	}
	// A subject no i32 offset could describe, and a start offset the engine's
	// u32 parameter could not hold, are refused here; every other offset, the
	// ones past the end of the subject included, is the engine's own BadInput,
	// and so is every configuration value that is not the default.
	if len(subject) > MaxLength {
		return nil, &Error{Kind: BadInput}
	}
	if start < 0 || uint64(start) > uint64(^uint32(0)) {
		return nil, &Error{Kind: BadInput}
	}
	if wideConfig(config) {
		return nil, &Error{Kind: BadInput}
	}
	if limits.Cost > MaxCostLimit || limits.Stack > MaxStackLimit ||
		limits.Memory > MaxMemoryLimit {
		return nil, &Error{Kind: BadInput}
	}
	var ovector []uint32
	var usage engine.Usage
	status := engine.Tir_match(
		re.program,
		subject,
		uint32(start),
		uint32(flags),
		uint32(config),
		limits.Cost,
		limits.Stack,
		limits.Memory,
		&ovector,
		&usage,
	)
	switch status {
	case statusMatched:
		offsets := make([]int32, len(ovector))
		for i, slot := range ovector {
			if slot == unset {
				offsets[i] = -1
			} else {
				offsets[i] = int32(slot)
			}
		}
		return offsets, nil
	case statusNoMatch:
		return nil, nil
	case statusResourceExceeded:
		return nil, &Error{Kind: ResourceExceeded}
	case statusBadInput:
		return nil, &Error{Kind: BadInput}
	}
	return nil, &Error{Kind: Internal, Code: int(status)}
}

// Class is what ComplexityClass answers. Linear is a proved claim — the cost
// of any match is at most a constant times the subject length plus one —
// while NotProvenLinear is the honest remainder: a conservative bound exists,
// possibly polynomial or exponential in form, and it may overestimate but
// never underestimate.
type Class int

const (
	NotProvenLinear Class = iota
	Linear
)

// ComplexityClass is the pattern's complexity class, fixed at compilation.
// It takes no configuration because no configuration changes it: memoization
// alters the constants of an eligible pattern, never the class. A pattern
// with no accepted bound certificate is ExceedsBudget, since a class claim
// with no certified bound behind it would be a claim about nothing.
func (re *Regexp) ComplexityClass() (Class, error) {
	value, err := answered(engine.Tir_re_class(re.program))
	return Class(value), err
}

// WorstCaseCost is the most a Match call on a subject of that length can be
// charged, in the cost units Limits.Cost is stated in, so the number can be
// passed there unchanged. The bound holds for every subject of that length,
// every start offset, and every combination of match flags.
func (re *Regexp) WorstCaseCost(subjectLen int, config MatchConfig) (uint64, error) {
	n, mcfg, err := asked(subjectLen, config)
	if err != nil {
		return 0, err
	}
	return answered(engine.Tir_re_cost(re.program, mcfg, n))
}

// WorstCaseStackEntries is the deepest the backtrack stack can get on such a
// call, in the entries Limits.Stack is stated in.
func (re *Regexp) WorstCaseStackEntries(subjectLen int, config MatchConfig) (uint32, error) {
	n, mcfg, err := asked(subjectLen, config)
	if err != nil {
		return 0, err
	}
	// The generated evaluator has already refused anything past the stack
	// ceiling, and that ceiling fits a uint32, so the narrowing is exact.
	value, err := answered(engine.Tir_re_stack(re.program, mcfg, n))
	return uint32(value), err
}

// WorstCaseMemory is the peak scratch reservation of such a call, in the IR
// bytes Limits.Memory is stated in.
func (re *Regexp) WorstCaseMemory(subjectLen int, config MatchConfig) (uint64, error) {
	n, mcfg, err := asked(subjectLen, config)
	if err != nil {
		return 0, err
	}
	return answered(engine.Tir_re_mem(re.program, mcfg, n))
}

// asked refuses what the engine's parameters could not carry — a negative or
// over-saturation length, a configuration past the u32 range; everything
// representable is the generated code's own decision, so the three languages
// refuse identically.
func asked(subjectLen int, config MatchConfig) (uint64, uint32, error) {
	if subjectLen < 0 || uint64(subjectLen) > counterCap {
		return 0, 0, &Error{Kind: BadInput}
	}
	if wideConfig(config) {
		return 0, 0, &Error{Kind: BadInput}
	}
	return uint64(subjectLen), uint32(config), nil
}

// wideConfig is the u32 door in one place: a configuration value past the
// engine's parameter range stays representable and is refused, never wrapped.
func wideConfig(config MatchConfig) bool {
	return uint64(config) > uint64(^uint32(0))
}

// answered turns a generated accessor answer into Go's shape: the number, or
// the *Error its status names.
func answered(answer engine.Answer) (uint64, error) {
	switch answer.Tir_status() {
	case statusOK:
		return answer.Tir_value(), nil
	case statusBadInput:
		return 0, &Error{Kind: BadInput}
	case statusExceedsBudget:
		return 0, &Error{Kind: ExceedsBudget}
	}
	return 0, &Error{Kind: Internal, Code: int(answer.Tir_status())}
}
