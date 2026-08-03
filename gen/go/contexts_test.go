package pcrevera

// The context section of the certificate corpus, run against the public Go
// wrapper, plus the operational claim the corpus cannot state: a match on a
// context allocates nothing, failure paths included. The same section runs
// against the Python interpreter and the generated JavaScript.

import (
	"bytes"
	"errors"
	"fmt"
	"slices"
	"testing"

	"github.com/PCRE-Vera/pcre-vera/gen/go/internal/corpustest"
)

type contextCreation struct {
	Config uint32  `json:"config"`
	Maxlen int     `json:"maxlen"`
	Cost   uint64  `json:"cost"`
	Stack  uint32  `json:"stack"`
	Memory uint64  `json:"memory"`
	Status uint32  `json:"status"`
	Memcap *uint64 `json:"memcap"`
}

// A nil cost or stack is the baked ceiling, which is what a caller who
// lowers nothing passes.
type contextCall struct {
	Subject string  `json:"subject"`
	Start   int     `json:"start"`
	Cost    *uint64 `json:"cost"`
	Stack   *uint32 `json:"stack"`
	Status  uint32  `json:"status"`
	Ovector []int32 `json:"ovector"`
}

type contextEntry struct {
	Name      string            `json:"name"`
	Note      string            `json:"note"`
	Pattern   string            `json:"pattern"`
	Maxlen    int               `json:"maxlen"`
	Creations []contextCreation `json:"creations"`
	Calls     []contextCall     `json:"calls"`
}

func kindOf(status uint32) Kind {
	switch status {
	case statusResourceExceeded:
		return ResourceExceeded
	case statusBadInput:
		return BadInput
	case statusExceedsBudget:
		return ExceedsBudget
	}
	return 0
}

func wantKind(t *testing.T, err error, status uint32, where string) {
	t.Helper()
	var failure *Error
	if !errors.As(err, &failure) {
		t.Fatalf("%s: expected an *Error for status %d, got %v", where, status, err)
	}
	if want := kindOf(status); failure.Kind != want {
		t.Fatalf("%s: expected kind %d, got %d", where, want, failure.Kind)
	}
}

func TestContextCorpus(t *testing.T) {
	entries, err := corpustest.Section[contextEntry](
		"../../conformance/certificates.json", "contexts")
	if err != nil {
		t.Fatal(err)
	}
	for _, entry := range entries {
		t.Run(entry.Name, func(t *testing.T) { runContextEntry(t, entry) })
	}
}

func runContextEntry(t *testing.T, entry contextEntry) {
	re, err := Compile(string(mustDecode(t, entry.Pattern)), Options{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	for _, row := range entry.Creations {
		where := entry.Name + ": " + entry.Note
		held, err := re.NewContext(
			row.Maxlen,
			Limits{Cost: row.Cost, Stack: row.Stack, Memory: row.Memory},
			MatchConfig(row.Config),
		)
		if row.Status != statusOK {
			wantKind(t, err, row.Status, where)
			continue
		}
		if err != nil {
			t.Fatalf("%s: creation failed: %v", where, err)
		}
		// The reservation is pinned twice over: the number the corpus wrote
		// down, and this wrapper's own memory accessor at the declared
		// length. Physical equality with the arrays themselves is asked
		// inside the generated package, where the arrays are visible.
		if row.Memcap == nil || held.Memory() != *row.Memcap {
			t.Fatalf("%s: reservation %d, corpus says %v", where, held.Memory(), row.Memcap)
		}
		bound, err := re.WorstCaseMemory(row.Maxlen, MatchConfig(row.Config))
		if err != nil || bound != held.Memory() {
			t.Fatalf(
				"%s: reservation %d, the accessor answers %d (%v)",
				where, held.Memory(), bound, err,
			)
		}
		if held.MaxSubjectLen() != row.Maxlen {
			t.Fatalf("%s: maxlen %d, want %d", where, held.MaxSubjectLen(), row.Maxlen)
		}
	}
	if len(entry.Calls) == 0 {
		return
	}

	first := entry.Creations[0]
	held, err := re.NewContext(
		entry.Maxlen,
		Limits{Cost: first.Cost, Stack: first.Stack, Memory: first.Memory},
		DefaultConfig,
	)
	if err != nil {
		t.Fatalf("creating the shared context: %v", err)
	}
	for i, call := range entry.Calls {
		where := fmt.Sprintf("%s: call %d", entry.Name, i)
		cost := first.Cost
		if call.Cost != nil {
			cost = *call.Cost
		}
		stack := first.Stack
		if call.Stack != nil {
			stack = *call.Stack
		}
		ovector, err := held.Match(mustDecode(t, call.Subject), call.Start, 0, cost, stack)
		switch call.Status {
		case statusMatched:
			if err != nil {
				t.Fatalf("%s: %v", where, err)
			}
			if !slices.Equal(ovector, call.Ovector) {
				t.Fatalf("%s: ovector %v, want %v", where, ovector, call.Ovector)
			}
		case statusNoMatch:
			if err != nil || ovector != nil {
				t.Fatalf("%s: expected no match, got %v, %v", where, ovector, err)
			}
		default:
			wantKind(t, err, call.Status, where)
		}
	}
}

// The operational half of the contract: once a context exists, matching on
// it performs no allocation at all — not on a match, not on a miss, and not
// on any refusal. This is what the reservation was for.
func TestContextMatchingAllocatesNothing(t *testing.T) {
	for _, tc := range []struct {
		name    string
		pattern string
		subject string
	}{
		// One pattern per execution path: the star rides the Pike VM, the
		// counted repetition stays on the backtracker.
		{"lockstep", "(a)(b*)", "xabb"},
		{"backtracking", "a{0,2}b*", "aabb"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			re := MustCompile(tc.pattern, Options{})
			held, err := re.NewContext(64, DefaultLimits(), DefaultConfig)
			if err != nil {
				t.Fatal(err)
			}
			matching := []byte(tc.subject)
			missing := []byte("zzz")
			tooLong := bytes.Repeat([]byte("a"), 65)
			caps := DefaultLimits()
			for _, path := range []struct {
				name string
				call func() ([]int32, error)
			}{
				{"match", func() ([]int32, error) {
					return held.Match(matching, 0, 0, caps.Cost, caps.Stack)
				}},
				{"no match", func() ([]int32, error) {
					return held.Match(missing, 0, 0, caps.Cost, caps.Stack)
				}},
				{"too long", func() ([]int32, error) {
					return held.Match(tooLong, 0, 0, caps.Cost, caps.Stack)
				}},
				{"raised limit", func() ([]int32, error) {
					return held.Match(matching, 0, 0, caps.Cost+1, caps.Stack)
				}},
				{"starved", func() ([]int32, error) {
					return held.Match(matching, 0, 0, 1, caps.Stack)
				}},
			} {
				if allocs := testing.AllocsPerRun(100, func() { _, _ = path.call() }); allocs != 0 {
					t.Fatalf("%s: %v allocations per call, want none", path.name, allocs)
				}
			}
		})
	}
}

// And the one allocation the API keeps, in the place it documents.
func TestCopyOvectorIsTheCopyOut(t *testing.T) {
	re := MustCompile("(a)(b*)", Options{})
	held, err := re.NewContext(16, DefaultLimits(), DefaultConfig)
	if err != nil {
		t.Fatal(err)
	}
	caps := DefaultLimits()
	first, err := held.Match([]byte("abb"), 0, 0, caps.Cost, caps.Stack)
	if err != nil {
		t.Fatal(err)
	}
	kept := CopyOvector(first)
	second, err := held.Match([]byte("xa"), 0, 0, caps.Cost, caps.Stack)
	if err != nil {
		t.Fatal(err)
	}
	// The view is the context's and moved on; the copy did not.
	if &first[0] != &second[0] {
		t.Fatal("expected the context to answer through one owned view")
	}
	if kept[0] != 0 || kept[1] != 3 || second[0] != 1 {
		t.Fatalf("expected the copy to hold the first answer, got %v and %v", kept, second)
	}
	if CopyOvector(nil) != nil {
		t.Fatal("copying a no-match is a no-match")
	}
}
