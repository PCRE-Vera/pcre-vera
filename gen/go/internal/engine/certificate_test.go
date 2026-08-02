package engine

// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated Go. The same file runs against the Python interpreter and the
// generated JavaScript, so agreeing with it is what "agreeing bit for bit"
// means.
//
// This test sits inside the generated package rather than beside the wrapper,
// because TIR field names are printed verbatim and Go cannot reach a lower-case
// field from another package. A certificate therefore has to be built here.

import (
	"encoding/json"
	"os"
	"testing"
)

const certificateSchema = 1

const certificatePath = "../../../../conformance/certificates.json"

type certSum struct {
	First uint32 `json:"first"`
	Count uint32 `json:"count"`
}

type certRegion struct {
	Kind   uint32  `json:"kind"`
	Parent uint32  `json:"parent"`
	Lo     uint32  `json:"lo"`
	Hi     uint32  `json:"hi"`
	Cost   certSum `json:"cost"`
	Stack  certSum `json:"stack"`
	Mem    certSum `json:"mem"`
}

type certTerm struct {
	Coef   uint64 `json:"coef"`
	Base   uint32 `json:"base"`
	Degree uint32 `json:"degree"`
}

type certBody struct {
	Config     uint32       `json:"config"`
	Complexity uint32       `json:"complexity"`
	Regions    []certRegion `json:"regions"`
	Terms      []certTerm   `json:"terms"`
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
	CodeLen uint32       `json:"codelen"`
	Cert    certBody     `json:"cert"`
	Check   uint32       `json:"check"`
	Bounds  []certBounds `json:"bounds"`
}

func readCertificates(t *testing.T) []certCase {
	t.Helper()
	raw, err := os.ReadFile(certificatePath)
	if err != nil {
		t.Fatal(err)
	}
	var document struct {
		Schema int        `json:"schema"`
		Cases  []certCase `json:"cases"`
	}
	if err := json.Unmarshal(raw, &document); err != nil {
		t.Fatal(err)
	}
	if document.Schema != certificateSchema {
		t.Fatalf("schema %d, want %d", document.Schema, certificateSchema)
	}
	if len(document.Cases) == 0 {
		t.Fatal("the certificate corpus holds no cases")
	}
	return document.Cases
}

func buildSum(one certSum) Sum {
	return Sum{first: one.First, count: one.Count}
}

func buildCert(body certBody) Cert {
	regions := make([]Region, len(body.Regions))
	for i, one := range body.Regions {
		regions[i] = Region{
			kind:   Rk(one.Kind),
			parent: one.Parent,
			lo:     one.Lo,
			hi:     one.Hi,
			cost:   buildSum(one.Cost),
			stack:  buildSum(one.Stack),
			mem:    buildSum(one.Mem),
		}
	}
	terms := make([]Term, len(body.Terms))
	for i, one := range body.Terms {
		terms[i] = Term{coef: one.Coef, base: one.Base, degree: one.Degree}
	}
	return Cert{
		config:     Cfg(body.Config),
		complexity: Cc(body.Complexity),
		regions:    regions,
		terms:      terms,
	}
}

func TestCertificateCorpus(t *testing.T) {
	for _, one := range readCertificates(t) {
		t.Run(one.Name, func(t *testing.T) {
			cert := buildCert(one.Cert)
			if got := Tir_cert_check(cert, one.CodeLen); uint32(got) != one.Check {
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
