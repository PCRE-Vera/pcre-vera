package engine

// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated Go. The same file runs against the Python interpreter and the
// generated JavaScript, so agreeing with it is what "agreeing bit for bit"
// means.
//
// Every case names a pattern rather than a bytecode listing, so this compiles
// it here and hands the checker the program this backend would really run. Two
// backends that disagree about the bytecode therefore disagree about the
// verdict, which is the point.
//
// This test sits inside the generated package rather than beside the wrapper.
// TIR field names are printed verbatim, so the printer's Tir_ facade can export
// readers for them but nothing that writes: a certificate can be read from
// outside the package and not built there. The alternative — teaching the
// printer to emit a constructor per copyable struct — is a lot of generated
// surface for one test, and the M5 accessors will read a certificate out of a
// compiled pattern rather than build one.

import (
	"encoding/hex"
	"testing"

	"github.com/jedisct1/pcre-truste/gen/go/internal/corpustest"
)

const certificatePath = "../../../../conformance/certificates.json"

type certPoly struct {
	Base uint64 `json:"base"`
	C0   uint64 `json:"c0"`
	C1   uint64 `json:"c1"`
	C2   uint64 `json:"c2"`
	C3   uint64 `json:"c3"`
	C4   uint64 `json:"c4"`
}

type certRegion struct {
	Kind   uint32   `json:"kind"`
	Parent uint32   `json:"parent"`
	Lo     uint32   `json:"lo"`
	Hi     uint32   `json:"hi"`
	Work   certPoly `json:"work"`
	Outs   certPoly `json:"outs"`
	Stack  certPoly `json:"stack"`
	Trail  certPoly `json:"trail"`
}

type certBody struct {
	Config     uint32       `json:"config"`
	Complexity uint32       `json:"complexity"`
	Cost       certPoly     `json:"cost"`
	Stack      certPoly     `json:"stack"`
	Mem        certPoly     `json:"mem"`
	Regions    []certRegion `json:"regions"`
}

// A nil bound is the ExceedsBudget of DESIGN.md section 2.4, which is a refusal
// rather than a number.
type certBounds struct {
	N     uint64  `json:"n"`
	Cost  *uint64 `json:"cost"`
	Stack *uint64 `json:"stack"`
	Mem   *uint64 `json:"mem"`
}

type certCase struct {
	Name    string       `json:"name"`
	Note    string       `json:"note"`
	Pattern string       `json:"pattern"`
	Config  uint32       `json:"config"`
	Cert    certBody     `json:"cert"`
	Check   uint32       `json:"check"`
	Bounds  []certBounds `json:"bounds"`
}

func readCertificates(t *testing.T) []certCase {
	t.Helper()
	cases, err := corpustest.Read[certCase](certificatePath)
	if err != nil {
		t.Fatal(err)
	}
	return cases
}

func buildPoly(one certPoly) Poly {
	return Poly{base: one.Base, c0: one.C0, c1: one.C1, c2: one.C2, c3: one.C3, c4: one.C4}
}

// A TIR enum value is one of the variants it declares, and once printed it is
// a number like any other, so a decoder that cast whatever the file held would
// hand the engine a value the IR has no meaning for. The Python side refuses a
// variant name its enum does not declare; this is the same refusal, spelt in
// the ordinals the file carries.
func variant(t *testing.T, what string, ordinal uint32, last uint32) uint32 {
	t.Helper()
	if ordinal > last {
		t.Fatalf("%s ordinal %d names no variant", what, ordinal)
	}
	return ordinal
}

func buildCert(t *testing.T, body certBody) Cert {
	regions := make([]Region, len(body.Regions))
	for i, one := range body.Regions {
		regions[i] = Region{
			kind:   Rk(variant(t, "Rk", one.Kind, uint32(RkRepeat))),
			parent: one.Parent,
			lo:     one.Lo,
			hi:     one.Hi,
			work:   buildPoly(one.Work),
			outs:   buildPoly(one.Outs),
			stack:  buildPoly(one.Stack),
			trail:  buildPoly(one.Trail),
		}
	}
	return Cert{
		config:     Cfg(variant(t, "Cfg", body.Config, uint32(CfgMemo))),
		complexity: Cc(variant(t, "Cc", body.Complexity, uint32(CcLinear))),
		cost:       buildPoly(body.Cost),
		stack:      buildPoly(body.Stack),
		mem:        buildPoly(body.Mem),
		regions:    regions,
	}
}

func buildProgram(t *testing.T, pattern string) Re {
	t.Helper()
	bytes, err := hex.DecodeString(pattern)
	if err != nil {
		t.Fatal(err)
	}
	var out Out
	Tir_compile(bytes, 0, 0, 0, &out)
	if code := out.Tir_err(); code != 0 {
		t.Fatalf("the pattern does not compile: error %d", code)
	}
	return out.Tir_re()
}

func TestCertificateCorpus(t *testing.T) {
	for _, one := range readCertificates(t) {
		t.Run(one.Name, func(t *testing.T) {
			cert := buildCert(t, one.Cert)
			re := buildProgram(t, one.Pattern)
			asked := Cfg(variant(t, "Cfg", one.Config, uint32(CfgMemo)))
			got := Tir_cert_check(re, asked, cert)
			if uint32(got) != one.Check {
				t.Fatalf("cert_check = %d, want %d (%s)", got, one.Check, one.Note)
			}
			for _, at := range one.Bounds {
				wantBound(t, "cost", Tir_cert_bound(cert, BkCost, at.N), at.Cost, at.N)
				wantBound(t, "stack", Tir_cert_bound(cert, BkStack, at.N), at.Stack, at.N)
				wantBound(t, "mem", Tir_cert_bound(cert, BkMem, at.N), at.Mem, at.N)
			}
		})
	}
}

func wantBound(t *testing.T, what string, got Bound, want *uint64, n uint64) {
	t.Helper()
	if want == nil {
		if got.ok {
			t.Fatalf("%s at n=%d is %d, want ExceedsBudget", what, n, got.value)
		}
		return
	}
	if !got.ok {
		t.Fatalf("%s at n=%d is ExceedsBudget, want %d", what, n, *want)
	}
	if got.value != *want {
		t.Fatalf("%s at n=%d is %d, want %d", what, n, got.value, *want)
	}
}
