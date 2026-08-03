package engine

// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated Go. The same file runs against the Python interpreter and the
// generated JavaScript, so agreeing with it is what "agreeing bit for bit"
// means.
//
// It has two halves, and so does this. The cases hand the checker a
// certificate; the analyses compile a pattern and read the one compilation
// produced. Either way the pattern is compiled here rather than described, so
// the engine is handed the program this backend would really run, and two
// backends that disagree about the bytecode therefore disagree about the
// answer.
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

	"github.com/PCRE-Vera/pcre-vera/gen/go/internal/corpustest"
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
	Kind   uint32 `json:"kind"`
	Parent uint32 `json:"parent"`
	Lo     uint32 `json:"lo"`
	Hi     uint32 `json:"hi"`
}

type certPrice struct {
	Work  certPoly `json:"work"`
	Outs  certPoly `json:"outs"`
	Stack certPoly `json:"stack"`
	Trail certPoly `json:"trail"`
}

type certBody struct {
	Config     uint32      `json:"config"`
	Complexity uint32      `json:"complexity"`
	Cost       certPoly    `json:"cost"`
	Stack      certPoly    `json:"stack"`
	Trail      certPoly    `json:"trail"`
	Mem        certPoly    `json:"mem"`
	Prices     []certPrice `json:"prices"`
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
	Shape   uint32       `json:"shape"`
	Bounds  []certBounds `json:"bounds"`
	// A region table to put in place of the one the compiler emitted, for the
	// cases about trees no compiler would emit. Absent from every other case.
	Regions []certRegion `json:"regions"`
}

// A null complexity is a pattern the analyzer found no representable bound
// for, which is an answer rather than a failure: the pattern compiles and has
// no certificate.
type certAnalysis struct {
	Name       string       `json:"name"`
	Note       string       `json:"note"`
	Pattern    string       `json:"pattern"`
	Found      uint32       `json:"found"`
	Complexity *uint32      `json:"complexity"`
	Bounds     []certBounds `json:"bounds"`
}

func readCertificates(t *testing.T) []certCase {
	t.Helper()
	cases, err := corpustest.Read[certCase](certificatePath)
	if err != nil {
		t.Fatal(err)
	}
	return cases
}

func readAnalyses(t *testing.T) []certAnalysis {
	t.Helper()
	held, err := corpustest.Section[certAnalysis](certificatePath, "analyses")
	if err != nil {
		t.Fatal(err)
	}
	return held
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
	prices := make([]Price, len(body.Prices))
	for i, one := range body.Prices {
		prices[i] = Price{
			work:  buildPoly(one.Work),
			outs:  buildPoly(one.Outs),
			stack: buildPoly(one.Stack),
			trail: buildPoly(one.Trail),
		}
	}
	return Cert{
		config:     Cfg(variant(t, "Cfg", body.Config, uint32(CfgMemo))),
		complexity: Cc(variant(t, "Cc", body.Complexity, uint32(CcLinear))),
		cost:       buildPoly(body.Cost),
		stack:      buildPoly(body.Stack),
		trail:      buildPoly(body.Trail),
		mem:        buildPoly(body.Mem),
		prices:     prices,
	}
}

func buildRegions(t *testing.T, held []certRegion) []Region {
	regions := make([]Region, len(held))
	for i, one := range held {
		regions[i] = Region{
			kind:   Rk(variant(t, "Rk", one.Kind, uint32(RkRepeat))),
			parent: one.Parent,
			lo:     one.Lo,
			hi:     one.Hi,
		}
	}
	return regions
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
			if one.Regions != nil {
				re.regions = buildRegions(t, one.Regions)
			}
			asked := Cfg(variant(t, "Cfg", one.Config, uint32(CfgMemo)))
			got := Tir_cert_check(re, asked, cert)
			if uint32(got) != one.Check {
				t.Fatalf("cert_check = %d, want %d (%s)", got, one.Check, one.Note)
			}
			// The checker without the certificate, which compilation runs on
			// its own. Which of the two halves answers each case is recorded
			// rather than derived here, so a check that moved from one half to
			// the other fails rather than passing either way.
			if shape := Tir_cert_shape(re); uint32(shape) != one.Shape {
				t.Fatalf("cert_shape = %d, want %d (%s)", shape, one.Shape, one.Note)
			}
			for _, at := range one.Bounds {
				wantBound(t, "cost", Tir_cert_bound(cert, BkCost, at.N), at.Cost, at.N)
				wantBound(t, "stack", Tir_cert_bound(cert, BkStack, at.N), at.Stack, at.N)
				wantBound(t, "mem", Tir_cert_bound(cert, BkMem, at.N), at.Mem, at.N)
			}
		})
	}
}

// The other half: no certificate is handed in, because compiling the pattern
// is what produces one. What the corpus records is the analyzer's own verdict,
// then the class and the bounds of whatever compilation stored — and for a
// pattern with no representable bound, that the slot stayed empty.
func TestCertificateAnalysis(t *testing.T) {
	for _, one := range readAnalyses(t) {
		t.Run(one.Name, func(t *testing.T) {
			re := buildProgram(t, one.Pattern)
			var cand Cert
			if found := Tir_cert_build(re, &cand); uint32(found) != one.Found {
				t.Fatalf("cert_build = %d, want %d (%s)", found, one.Found, one.Note)
			}
			if one.Complexity == nil {
				if re.hascert {
					t.Fatalf("a pattern with no bound carries one (%s)", one.Note)
				}
				return
			}
			if !re.hascert {
				t.Fatalf("compiling stored no certificate (%s)", one.Note)
			}
			// Both of them: the certificate compiling stored, and the one the
			// analyzer just handed back. A backend where those two differ has
			// a compilation that kept something other than what it computed,
			// which nothing else here would notice.
			for _, pair := range []struct {
				what string
				cert Cert
			}{{"stored", re.cert}, {"built", cand}} {
				what, cert := pair.what, pair.cert
				if uint32(cert.complexity) != *one.Complexity {
					t.Fatalf(
						"%s complexity = %d, want %d (%s)",
						what, cert.complexity, *one.Complexity, one.Note,
					)
				}
				for _, at := range one.Bounds {
					wantBound(t, what+" cost", Tir_cert_bound(cert, BkCost, at.N), at.Cost, at.N)
					wantBound(t, what+" stack", Tir_cert_bound(cert, BkStack, at.N), at.Stack, at.N)
					wantBound(t, what+" mem", Tir_cert_bound(cert, BkMem, at.N), at.Mem, at.N)
				}
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

// A region kind outside the enum is not a TIR value at all, and in Go it is a
// number like any other. What matters is that the checker says so rather than
// pricing the region at nothing, which would hide every instruction in its
// range behind a claim of zero.
func TestARegionKindOutsideTheEnumIsRefused(t *testing.T) {
	one := Poly{base: 1}
	re := buildProgram(t, hex.EncodeToString([]byte("a?")))
	prices := make([]Price, len(re.regions))
	for i := range prices {
		prices[i] = Price{work: one, outs: one, stack: one, trail: one}
	}
	cert := Cert{cost: one, stack: one, trail: one, mem: one, prices: prices}
	if len(prices) < 2 {
		t.Fatalf("expected a tree with a region under the root, got %d", len(prices))
	}
	// Claiming one of everything is far too little, so the answer is about the
	// numbers. What matters is that it is about the numbers at all.
	if got := Tir_cert_check(re, CfgBacktrack, cert); got != CrRegionWork {
		t.Fatalf("cert_check = %d, want CrRegionWork (%d)", got, CrRegionWork)
	}
	re.regions[len(re.regions)-1].kind = Rk(999)
	if got := Tir_cert_check(re, CfgBacktrack, cert); got != CrShape {
		t.Fatalf("cert_check = %d, want CrShape (%d)", got, CrShape)
	}
	// A complexity class outside the enum is the same thing said of a field
	// rather than of a region: treating it as "not proven linear" would let a
	// caller name a class the engine has no claim for.
	re.regions[len(re.regions)-1].kind = RkRepeat
	cert.complexity = Cc(999)
	if got := Tir_cert_check(re, CfgBacktrack, cert); got != CrShape {
		t.Fatalf("cert_check = %d, want CrShape (%d)", got, CrShape)
	}
	if got := Tir_cert_bound(Cert{}, Bk(999), 4); got.ok {
		t.Fatalf("a bound of no kind is %d, want ExceedsBudget", got.value)
	}
}
