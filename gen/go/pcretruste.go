// Package pcretruste is the Go form of the pcre-truste engine: a thin,
// hand-written wrapper around the code generated from the TIR artifact, giving
// it the API of DESIGN.md section 2.4 with Go conventions.
//
// This release is provisional and says so rather than implying otherwise.
// Every pattern runs on the backtracking matcher, because matcher selection
// arrives with the Pike VM in M5. The analysis accessors — complexity class,
// worst-case cost, stack and memory — are the next slice of it: compiling
// already prices a pattern, and nothing reads the answer out yet. The
// preallocated match context and the match configuration argument follow. What
// works today is compile and match, under the caller's hard limits.
//
// A compiled pattern is immutable, so one may be shared across goroutines; a
// match call keeps all of its state on its own stack and in scratch it
// allocates itself.
//
// The subject is a byte sequence and stays one: string conveniences arrive
// with UTF mode in wave 3. The pattern is a Go string because a Go string
// already is an arbitrary byte sequence.
package pcretruste

import (
	"maps"
	"strconv"

	"github.com/jedisct1/pcre-truste/gen/go/internal/engine"
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
		return "pcre-truste: syntax error " + strconv.Itoa(e.Code) +
			" at offset " + strconv.Itoa(e.Offset)
	case UnsupportedFeature:
		return "pcre-truste: this release does not support that construct, at offset " +
			strconv.Itoa(e.Offset)
	case UnsupportedOption:
		return "pcre-truste: this release does not support that option"
	case PatternTooLarge:
		return "pcre-truste: the pattern is past a documented portable limit"
	case ResourceExceeded:
		return "pcre-truste: the match went over its cost, stack or memory limit"
	case BadInput:
		return "pcre-truste: an argument is outside its documented range"
	}
	return "pcre-truste: internal error " + strconv.Itoa(e.Code)
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
	statusNoMatch          = 1
	statusResourceExceeded = 2
	statusBadInput         = 3

	unset = 0xFFFFFFFF
)

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
// limits, and returns the ovector: byte offsets of the whole match at entries
// 0 and 1, then a pair for every capturing group. A group that did not
// participate reports -1 for both ends.
//
// A subject that does not match is a nil ovector and a nil error. Everything
// else — a budget exhausted, a start offset outside the subject, a limit past
// what any target could honor — is an *Error.
func (re *Regexp) Match(
	subject []byte,
	start int,
	flags MatchFlags,
	limits Limits,
) ([]int32, error) {
	if flags&^knownMatchFlags != 0 {
		return nil, &Error{Kind: UnsupportedOption, Code: codeUnsupportedOption}
	}
	// A subject no i32 offset could describe, and a start offset the engine's
	// u32 parameter could not hold, are refused here; every other offset, the
	// ones past the end of the subject included, is the engine's own BadInput.
	if len(subject) > MaxLength {
		return nil, &Error{Kind: BadInput}
	}
	if start < 0 || uint64(start) > uint64(^uint32(0)) {
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
