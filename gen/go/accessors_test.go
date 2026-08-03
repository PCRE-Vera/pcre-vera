package pcrevera

// The accessors section of the certificate corpus, asked through the public
// wrapper: the same statuses and the same numbers as the Python driver and
// the JavaScript wrapper, and for every query marked exercise, a match at
// exactly the pinned bounds that must not run out of them. It lives beside
// the wrapper rather than inside the generated package because its whole
// point is to reach the numbers the way an application would.

import (
	"bytes"
	"errors"
	"testing"

	"github.com/PCRE-Vera/pcre-vera/gen/go/internal/corpustest"
)

type accessorAnswer struct {
	Status uint32 `json:"status"`
	Value  uint64 `json:"value"`
}

type accessorQuery struct {
	Config   uint32         `json:"config"`
	N        uint64         `json:"n"`
	Cost     accessorAnswer `json:"cost"`
	Stack    accessorAnswer `json:"stack"`
	Mem      accessorAnswer `json:"mem"`
	Exercise bool           `json:"exercise"`
}

type accessorCase struct {
	Name    string          `json:"name"`
	Note    string          `json:"note"`
	Pattern string          `json:"pattern"`
	Class   accessorAnswer  `json:"class"`
	Queries []accessorQuery `json:"queries"`
}

// The accessors section of the certificate corpus, asked through the public
// wrapper: the same statuses and the same numbers as the other two languages,
// and for every query marked exercise, a match at exactly the pinned bounds
// that must not run out of them.
func TestAccessorCorpus(t *testing.T) {
	cases, err := corpustest.Section[accessorCase](
		"../../conformance/certificates.json", "accessors")
	if err != nil {
		t.Fatal(err)
	}
	for _, one := range cases {
		t.Run(one.Name, func(t *testing.T) { runAccessorCase(t, one) })
	}
}

func runAccessorCase(t *testing.T, one accessorCase) {
	re, err := Compile(string(mustDecode(t, one.Pattern)), Options{})
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	class, err := re.ComplexityClass()
	if got := answerOf(t, uint64(class), err); got != one.Class {
		t.Fatalf("complexity class answers %+v, the corpus says %+v: %s",
			got, one.Class, one.Note)
	}
	for _, q := range one.Queries {
		n, config := int(q.N), MatchConfig(q.Config)
		cost, err := re.WorstCaseCost(n, config)
		if got := answerOf(t, cost, err); got != q.Cost {
			t.Fatalf("cost at n=%d config=%d answers %+v, want %+v", n, config, got, q.Cost)
		}
		stack, err := re.WorstCaseStackEntries(n, config)
		if got := answerOf(t, uint64(stack), err); got != q.Stack {
			t.Fatalf("stack at n=%d config=%d answers %+v, want %+v", n, config, got, q.Stack)
		}
		mem, err := re.WorstCaseMemory(n, config)
		if got := answerOf(t, mem, err); got != q.Mem {
			t.Fatalf("mem at n=%d config=%d answers %+v, want %+v", n, config, got, q.Mem)
		}
		if !q.Exercise {
			continue
		}
		// The three bounds unchanged as the limits, which the Limits types are
		// shaped to allow, and a run that may find or not find but not run out.
		limits := Limits{Cost: cost, Stack: stack, Memory: mem}
		subject := bytes.Repeat([]byte{'a'}, n)
		if _, err := re.Match(subject, 0, 0, limits, DefaultConfig); err != nil {
			t.Fatalf("a match at the pinned bounds failed at n=%d: %v", n, err)
		}
	}
}

func answerOf(t *testing.T, value uint64, err error) accessorAnswer {
	t.Helper()
	if err == nil {
		return accessorAnswer{Status: statusOK, Value: value}
	}
	var failure *Error
	if !errors.As(err, &failure) {
		t.Fatalf("an accessor failed with something besides *Error: %v", err)
	}
	switch failure.Kind {
	case BadInput:
		return accessorAnswer{Status: statusBadInput}
	case ExceedsBudget:
		return accessorAnswer{Status: statusExceedsBudget}
	}
	t.Fatalf("an accessor failed with an unexpected kind: %v", err)
	return accessorAnswer{}
}
