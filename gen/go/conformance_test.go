package pcretruste

// The conformance corpus of DESIGN.md section 8, run against the generated Go.
// The same file runs against the Python interpreter and the generated
// JavaScript, so agreeing with it is what "agreeing bit for bit" means.

import (
	"encoding/hex"
	"errors"
	"slices"
	"testing"

	"github.com/jedisct1/pcre-truste/gen/go/internal/corpustest"
	"github.com/jedisct1/pcre-truste/gen/go/internal/probe"
)

type expectation struct {
	Kind     string         `json:"kind"`
	Ovector  []int32        `json:"ovector"`
	Code     int            `json:"code"`
	Offset   int            `json:"offset"`
	Captures int            `json:"captures"`
	Names    map[string]int `json:"names"`
}

type conformanceCase struct {
	Name       string      `json:"name"`
	Pattern    string      `json:"pattern"`
	Flags      uint32      `json:"flags"`
	Newline    uint32      `json:"newline"`
	BSR        uint32      `json:"bsr"`
	Subject    *string     `json:"subject"`
	MatchFlags uint32      `json:"matchFlags"`
	Start      int         `json:"start"`
	Expect     expectation `json:"expect"`
}

func readCorpus[T any](t *testing.T, path string) []T {
	t.Helper()
	cases, err := corpustest.Read[T](path)
	if err != nil {
		t.Fatal(err)
	}
	return cases
}

func mustDecode(t *testing.T, text string) []byte {
	t.Helper()
	raw, err := hex.DecodeString(text)
	if err != nil {
		t.Fatal(err)
	}
	return raw
}

func TestConformanceCorpus(t *testing.T) {
	cases := readCorpus[conformanceCase](t, "../../conformance/corpus.json")
	for _, one := range cases {
		t.Run(one.Name, func(t *testing.T) { runConformanceCase(t, one) })
	}
}

func runConformanceCase(t *testing.T, one conformanceCase) {
	pattern := string(mustDecode(t, one.Pattern))
	re, err := Compile(pattern, Options{
		Flags:   Flags(one.Flags),
		Newline: Newline(one.Newline),
		BSR:     BSR(one.BSR),
	})

	if one.Expect.Kind == "compileError" {
		var failure *Error
		if !errors.As(err, &failure) {
			t.Fatalf("expected compile error %d, got %v", one.Expect.Code, err)
		}
		if failure.Code != one.Expect.Code || failure.Offset != one.Expect.Offset {
			t.Fatalf("expected error %d at offset %d, got %d at offset %d",
				one.Expect.Code, one.Expect.Offset, failure.Code, failure.Offset)
		}
		return
	}
	if err != nil {
		t.Fatalf("compile: %v", err)
	}

	if one.Expect.Kind == "compiled" {
		if re.NumSubexp() != one.Expect.Captures {
			t.Fatalf("expected %d capture groups, got %d", one.Expect.Captures, re.NumSubexp())
		}
		names := re.SubexpNames()
		if len(names) != len(one.Expect.Names) {
			t.Fatalf("expected group names %v, got %v", one.Expect.Names, names)
		}
		for encoded, number := range one.Expect.Names {
			name := string(mustDecode(t, encoded))
			if got := re.SubexpIndex(name); got != number {
				t.Fatalf("expected group %q to be %d, got %d", name, number, got)
			}
		}
		return
	}

	if one.Subject == nil {
		t.Fatalf("a %s case needs a subject", one.Expect.Kind)
	}
	ovector, err := re.Match(
		mustDecode(t, *one.Subject),
		one.Start,
		MatchFlags(one.MatchFlags),
		DefaultLimits(),
	)
	if err != nil {
		t.Fatalf("match: %v", err)
	}
	if one.Expect.Kind == "nomatch" {
		if ovector != nil {
			t.Fatalf("expected no match, got %v", ovector)
		}
		return
	}
	if !slices.Equal(ovector, one.Expect.Ovector) {
		t.Fatalf("expected ovector %v, got %v", one.Expect.Ovector, ovector)
	}
}

type loweringCase struct {
	Name   string `json:"name"`
	Kind   uint32 `json:"kind"`
	A      uint64 `json:"a"`
	B      uint64 `json:"b"`
	Expect uint64 `json:"expect"`
}

// The lowering probe is not part of the library. It exists so that the places
// where a printer can be silently wrong — a product that needs more than 53
// bits, a struct read that aliases, a growth schedule that rounds differently —
// are asked about directly rather than only through the engine.
func TestLoweringProbe(t *testing.T) {
	cases := readCorpus[loweringCase](t, "../../conformance/lowering.json")
	for _, one := range cases {
		got := probe.Tir_probe(one.Kind, one.A, one.B)
		if got != one.Expect {
			t.Fatalf("%s(%d, %d) = %d, want %d", one.Name, one.A, one.B, got, one.Expect)
		}
	}
}
