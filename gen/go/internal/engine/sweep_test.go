package engine

// The committed shard of the differential sweep (DESIGN.md section 8), run
// against the generated Go. The same file runs against the Python interpreter
// and the generated JavaScript, so agreeing with it is what "agreeing bit for
// bit" means — and since the Python side has already agreed with pcre2 on
// every one of these cases, agreeing with the file is agreeing with pcre2.
//
// This sits inside the generated package rather than beside the wrapper for
// one reason: the resource half of the sweep is about `Usage`, which the
// public API does not return. Reaching the generated entry points here keeps
// the observed cost, stack and memory of every trial under test without
// widening the surface the wrapper promises, and the wrapper stays covered by
// the conformance and certificate runners next door.
//
// The three checks of section 8, in the order the record carries them: the
// semantic one is the outcome and the ovector, the cross-matcher one is the
// backtracking matcher on a Pike-eligible program under its own analyzer's
// bounds, and the resource one is the observed usage against the certificate,
// the three limits at the observed value and one below, and a preallocated
// context created at exactly its reservation and one byte under it.

import (
	"encoding/hex"
	"os"
	"strconv"
	"sync"
	"testing"

	"github.com/PCRE-Vera/pcre-vera/gen/go/internal/corpustest"
)

const shardPath = "../../../../conformance/sweep.json"

// Which sweep to replay. The committed shard by default, and whatever a
// campaign wrote when PCREVERA_SWEEP names it: the result document of a run of
// `python -m pcrevera.sweep run` has exactly this shape, so the campaign that
// closes a milestone can be replayed here rather than only in the language
// that produced it.
func sweepPath() string {
	if named := os.Getenv("PCREVERA_SWEEP"); named != "" {
		return named
	}
	return shardPath
}

// The unset ovector sentinel, which the record spells as -1 the way every
// caller-facing surface does.
const sweepUnset = 0xFFFFFFFF

const (
	statusMatched  = 0
	statusNoMatch  = 1
	statusRefused  = 2
	statusBadInput = 3
	statusExceeds  = 4
)

// The codes this engine refuses with rather than pcre2's, from
// src/pcrevera/engine/spec.py. Which of them carries an offset is a contract
// rather than a property of the record: a construct or an option outside the
// claimed subset is refused at the byte that asked for it, and a pattern past
// a documented limit is refused about itself. Reading that off the presence of
// a field would mean a record that dropped its offset was replayed as a record
// that never had one.
const (
	codeUnsupportedFeature = 1000
	codeUnsupportedOption  = 1001
	codePatternTooLarge    = 1002
)

type sweepUsage struct {
	Cost  uint64 `json:"cost"`
	Stack uint32 `json:"stack"`
	Mem   uint64 `json:"mem"`
}

// A null bound is the ExceedsBudget of DESIGN.md section 2.4, which is a
// refusal rather than a number.
type sweepBound struct {
	Cost  *uint64 `json:"cost"`
	Stack *uint64 `json:"stack"`
	Mem   *uint64 `json:"mem"`
}

type sweepCross struct {
	Bound   sweepBound `json:"bound"`
	Outcome uint32     `json:"outcome"`
	Usage   sweepUsage `json:"usage"`
	Ovector []int32    `json:"ovector"`
	Edges   bool       `json:"edges"`
}

type sweepTrial struct {
	Subject    string      `json:"subject"`
	MatchFlags uint32      `json:"matchFlags"`
	Start      uint32      `json:"start"`
	Bound      sweepBound  `json:"bound"`
	Outcome    uint32      `json:"outcome"`
	Ovector    []int32     `json:"ovector"`
	Usage      sweepUsage  `json:"usage"`
	Edges      bool        `json:"edges"`
	Cross      *sweepCross `json:"cross"`
}

type sweepCall struct {
	Outcome uint32     `json:"outcome"`
	Usage   sweepUsage `json:"usage"`
}

type sweepContext struct {
	Status uint32      `json:"status"`
	Memcap uint64      `json:"memcap"`
	Calls  []sweepCall `json:"calls"`
	Edges  *int        `json:"edges"`
}

// A compile outcome is one of three. "compiled" carries the identity of the
// program; "compileError" is a pcre2 error the engine reproduces; "declined"
// is one of our own codes for a construct outside the claimed subset or a
// pattern past a documented limit, which pcre2 has no opinion about and every
// implementation of this engine still has to refuse identically. A declined
// case carries an offset only where the contract has one.
type sweepCompile struct {
	Kind     string            `json:"kind"`
	Code     uint32            `json:"code"`
	Offset   *uint32           `json:"offset"`
	Captures uint32            `json:"captures"`
	Names    map[string]uint32 `json:"names"`
}

type sweepCase struct {
	Name string `json:"name"`
	// A kept regression was found under limits of its own and goes on guarding
	// under them; a generated case runs under the document's. Absent on the
	// latter, which is what the two loaders below tell them apart by.
	Budget  *sweepBudget `json:"budget"`
	Index   int          `json:"index"`
	Family  string       `json:"family"`
	Pattern string       `json:"pattern"`
	Flags   uint32       `json:"flags"`
	Newline uint32       `json:"newline"`
	BSR     uint32       `json:"bsr"`
	Maxlen  uint32       `json:"maxlen"`
	Compile sweepCompile `json:"compile"`
	Pike    bool         `json:"pike"`
	Cert    struct {
		Backtrack bool `json:"backtrack"`
		Pike      bool `json:"pike"`
	} `json:"cert"`
	Class   *uint64      `json:"class"`
	Trials  []sweepTrial `json:"trials"`
	Context sweepContext `json:"context"`
}

type sweepBudget struct {
	Cost   uint64 `json:"cost"`
	Stack  uint32 `json:"stack"`
	Memory uint64 `json:"memory"`
}

type sweepLimits struct {
	cost   uint64
	stack  uint32
	memory uint64
}

// The whole document, read and parsed once. A campaign's own result document
// has this shape too and runs to tens of megabytes, so reading it per section
// would be seconds of parsing before the first case ran.
//
// The two optional-looking fields are pointers on purpose. A slice decodes the
// same way whether its key was absent or empty, and the difference is the
// whole contract: a repository that has kept no regression yet writes an empty
// list, while a document with no such key is one this runner cannot say it has
// replayed. A budget that decoded to its zero value would refuse every call
// and blame the engine.
type sweepDocument struct {
	Cases       []sweepCase  `json:"cases"`
	Regressions *[]sweepCase `json:"regressions"`
	Budget      *sweepBudget `json:"budget"`
}

var (
	sweepOnce  sync.Once
	sweepHeld  sweepDocument
	sweepError error
)

func sweepLoaded(t *testing.T) sweepDocument {
	t.Helper()
	sweepOnce.Do(func() {
		sweepError = corpustest.Into(sweepPath(), &sweepHeld)
	})
	if sweepError != nil {
		t.Fatal(sweepError)
	}
	if len(sweepHeld.Cases) == 0 {
		t.Fatalf("%s holds no cases", sweepPath())
	}
	if sweepHeld.Regressions == nil {
		t.Fatalf("%s has no regressions", sweepPath())
	}
	if sweepHeld.Budget == nil {
		t.Fatalf("%s has no budget", sweepPath())
	}
	return sweepHeld
}

// What to run at: the certificate's own number, never more than the sweep's
// budget. Both sides of the file compute this the same way from the recorded
// bound, so a backend whose accessors disagree runs at different limits and
// fails on the usage rather than passing quietly.
func sweepLimitsFor(bound sweepBound, budget sweepBudget) sweepLimits {
	out := sweepLimits{cost: budget.Cost, stack: budget.Stack, memory: budget.Memory}
	if bound.Cost != nil && *bound.Cost < out.cost {
		out.cost = *bound.Cost
	}
	if bound.Stack != nil && *bound.Stack < uint64(out.stack) {
		out.stack = uint32(*bound.Stack)
	}
	if bound.Mem != nil && *bound.Mem < out.memory {
		out.memory = *bound.Mem
	}
	return out
}

func sweepBytes(t *testing.T, text string) []byte {
	t.Helper()
	raw, err := hex.DecodeString(text)
	if err != nil {
		t.Fatal(err)
	}
	return raw
}

func sweepOffsets(ov []uint32) []int32 {
	out := make([]int32, len(ov))
	for i, slot := range ov {
		if slot == sweepUnset {
			out[i] = -1
		} else {
			out[i] = int32(slot)
		}
	}
	return out
}

func sameOffsets(a []int32, b []int32) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func sameUsage(got Usage, want sweepUsage) bool {
	return got.cost == want.Cost && got.stack == want.Stack && got.mem == want.Mem
}

func sweepRefused(t *testing.T, out Out, code uint32, offset uint32) {
	t.Helper()
	if out.err != code || out.erroff != offset {
		t.Fatalf("compile: error %d at %d, want %d at %d", out.err, out.erroff, code, offset)
	}
}

func sweepCompiled(t *testing.T, one sweepCase) (Re, bool) {
	t.Helper()
	var out Out
	Tir_compile(sweepBytes(t, one.Pattern), one.Flags, one.Newline, one.BSR, &out)
	// Three kinds and no others: a record whose kind nobody recognizes is a
	// record this runner cannot check, and passing it because its code matched
	// would be reporting a case as replayed when it was not.
	switch one.Compile.Kind {
	case "compileError":
		// A pcre2 error is refused at a byte, and the offset is part of it.
		if one.Compile.Offset == nil {
			t.Fatalf("compile: a compileError record carries no offset")
		}
		sweepRefused(t, out, one.Compile.Code, *one.Compile.Offset)
		return Re{}, false
	case "declined":
		switch one.Compile.Code {
		case codeUnsupportedFeature, codeUnsupportedOption:
			if one.Compile.Offset == nil {
				t.Fatalf("compile: a %d record carries no offset", one.Compile.Code)
			}
			sweepRefused(t, out, one.Compile.Code, *one.Compile.Offset)
		case codePatternTooLarge:
			if one.Compile.Offset != nil {
				t.Fatalf("compile: a %d record carries an offset its contract has not",
					one.Compile.Code)
			}
			if out.err != one.Compile.Code {
				t.Fatalf("compile: error %d, want %d", out.err, one.Compile.Code)
			}
		default:
			t.Fatalf("compile: %d is not a code this engine declines with",
				one.Compile.Code)
		}
		return Re{}, false
	case "compiled":
	default:
		t.Fatalf("compile: %q is not a compile outcome this runner knows", one.Compile.Kind)
	}
	if out.err != 0 {
		t.Fatalf("compile: error %d at offset %d, want a compiled pattern", out.err, out.erroff)
	}
	re := out.re
	if re.ncap != one.Compile.Captures {
		t.Fatalf("compile: %d capture groups, want %d", re.ncap, one.Compile.Captures)
	}
	names := map[string]uint32{}
	for _, ent := range re.nameents {
		names[hex.EncodeToString(re.names[ent.off:ent.off+ent.nlen])] = ent.grp
	}
	if len(names) != len(one.Compile.Names) {
		t.Fatalf("compile: group names %v, want %v", names, one.Compile.Names)
	}
	for name, number := range one.Compile.Names {
		if names[name] != number {
			t.Fatalf("compile: group %q is %d, want %d", name, names[name], number)
		}
	}
	return re, true
}

// The analysis the record pins before any subject is tried: which matcher
// compilation selected, which configurations carry a certificate, and the
// complexity class the public accessor answers.
func sweepAnalysis(t *testing.T, re Re, one sweepCase) {
	t.Helper()
	if re.pike != one.Pike {
		t.Fatalf("pike eligibility is %v, want %v", re.pike, one.Pike)
	}
	if re.hascert != one.Cert.Backtrack || re.haspikecert != one.Cert.Pike {
		t.Fatalf("certificates are %v/%v, want %v/%v",
			re.hascert, re.haspikecert, one.Cert.Backtrack, one.Cert.Pike)
	}
	held := Tir_re_class(re)
	if one.Class == nil {
		if held.status != statusExceeds {
			t.Fatalf("the class accessor answers %v, want ExceedsBudget", held)
		}
	} else if held.status != 0 || held.value != *one.Class {
		t.Fatalf("the class accessor answers %v, want %d", held, *one.Class)
	}
}

func sweepAccessors(t *testing.T, re Re, n uint64, want sweepBound) {
	t.Helper()
	for _, which := range []struct {
		name string
		got  Answer
		want *uint64
	}{
		{"cost", Tir_re_cost(re, 0, n), want.Cost},
		{"stack", Tir_re_stack(re, 0, n), want.Stack},
		{"mem", Tir_re_mem(re, 0, n), want.Mem},
	} {
		if which.want == nil {
			if which.got.status != statusExceeds {
				t.Fatalf("the %s accessor answers %v at n=%d, want ExceedsBudget",
					which.name, which.got, n)
			}
			continue
		}
		if which.got.status != 0 || which.got.value != *which.want {
			t.Fatalf("the %s accessor answers %v at n=%d, want %d",
				which.name, which.got, n, *which.want)
		}
	}
}

type sweepAnswer struct {
	status  uint32
	ovector []int32
	usage   Usage
}

// One call, on the selected path or on the backtracking one. The two entry
// points take the same arguments and mean the same thing, so the resource
// checks below are asked of either by handing them a different matcher.
type sweepMatcher func(Re, []byte, sweepTrial, sweepLimits) sweepAnswer

func sweepMatch(re Re, subject []byte, trial sweepTrial, limits sweepLimits) sweepAnswer {
	var ov []uint32
	var use Usage
	status := Tir_match(re, subject, trial.Start, trial.MatchFlags, 0,
		limits.cost, limits.stack, limits.memory, &ov, &use)
	return sweepAnswer{status: status, ovector: sweepOffsets(ov), usage: use}
}

func sweepBacktrack(re Re, subject []byte, trial sweepTrial, limits sweepLimits) sweepAnswer {
	var ov []uint32
	var use Usage
	status := Tir_bt_match(re, subject, trial.Start, trial.MatchFlags,
		limits.cost, limits.stack, limits.memory, &ov, &use)
	return sweepAnswer{status: status, ovector: sweepOffsets(ov), usage: use}
}

func sweepTrialRun(t *testing.T, re Re, one sweepCase, at int, budget sweepBudget) {
	t.Helper()
	trial := one.Trials[at]
	subject := sweepBytes(t, trial.Subject)
	sweepAccessors(t, re, uint64(len(subject)), trial.Bound)
	limits := sweepLimitsFor(trial.Bound, budget)
	got := sweepMatch(re, subject, trial, limits)
	if got.status != trial.Outcome {
		t.Fatalf("trial %d: outcome %d, want %d", at, got.status, trial.Outcome)
	}
	if trial.Outcome == statusMatched && !sameOffsets(got.ovector, trial.Ovector) {
		t.Fatalf("trial %d: ovector %v, want %v", at, got.ovector, trial.Ovector)
	}
	if !sameUsage(got.usage, trial.Usage) {
		t.Fatalf("trial %d: usage %+v, want %+v", at, got.usage, trial.Usage)
	}
	if trial.Edges {
		sweepEdges(t, sweepMatch, re, subject, trial, trial.Usage, limits, got, at)
	}
	if trial.Cross != nil {
		sweepCrossMatcher(t, re, subject, one, at, budget)
	}
}

// Each limit at the observed value and one below it: the deterministic budget
// boundary of DESIGN.md section 8. At the observed value the run gives exactly
// the answer it just gave; one unit below, it is refused. A dimension whose
// observed value is zero has no "one below" to ask about.
func sweepEdges(
	t *testing.T,
	run sweepMatcher,
	re Re,
	subject []byte,
	trial sweepTrial,
	used sweepUsage,
	limits sweepLimits,
	got sweepAnswer,
	at int,
) {
	t.Helper()
	for _, dimension := range []string{"cost", "stack", "mem"} {
		observed, edge := sweepAtEdge(limits, used, dimension, 0)
		again := run(re, subject, trial, edge)
		if again.status != got.status || !sameOffsets(again.ovector, got.ovector) {
			t.Fatalf("trial %d: at the observed %s limit %d the run answered %d %v, want %d %v",
				at, dimension, observed, again.status, again.ovector, got.status, got.ovector)
		}
		if observed == 0 {
			continue
		}
		_, below := sweepAtEdge(limits, used, dimension, 1)
		refused := run(re, subject, trial, below)
		if refused.status != statusRefused {
			t.Fatalf("trial %d: one below the observed %s limit %d the run answered %d, "+
				"want ResourceExceeded", at, dimension, observed, refused.status)
		}
	}
}

// The limits with one dimension moved to the observed value, less `down`.
func sweepAtEdge(limits sweepLimits, used sweepUsage, dimension string, down uint64) (uint64, sweepLimits) {
	out := limits
	switch dimension {
	case "cost":
		out.cost = used.Cost - down
		return used.Cost, out
	case "stack":
		out.stack = used.Stack - uint32(down)
		return uint64(used.Stack), out
	default:
		out.memory = used.Mem - down
		return used.Mem, out
	}
}

// The other matcher on the same trial, under its own analyzer's bounds. The
// selected path on a Pike-eligible program is the Pike VM, so what this adds
// is the backtracking run; where the backtracking analyzer has no finite
// certificate the record says so and the pair is not an agreement to be had.
//
// The backtracking bound is checked here rather than through the accessors,
// which answer for the selected path only. A backend whose backtracking
// analyzer drifted would otherwise be caught only where the drift moved an
// outcome, and under limits both the old and the new bound allow it would not.
func sweepCrossMatcher(t *testing.T, re Re, subject []byte, one sweepCase, at int, budget sweepBudget) {
	t.Helper()
	trial := one.Trials[at]
	bound := sweepBound{}
	if re.hascert {
		for _, which := range []struct {
			kind Bk
			slot **uint64
		}{{BkCost, &bound.Cost}, {BkStack, &bound.Stack}, {BkMem, &bound.Mem}} {
			if held := Tir_cert_bound(re.cert, which.kind, uint64(len(subject))); held.ok {
				value := held.value
				*which.slot = &value
			}
		}
	}
	sameBound(t, "the backtracking", bound, trial.Cross.Bound, at)
	limits := sweepLimitsFor(bound, budget)
	got := sweepBacktrack(re, subject, trial, limits)
	if got.status != trial.Cross.Outcome {
		t.Fatalf("trial %d: the backtracking matcher answered %d, want %d",
			at, got.status, trial.Cross.Outcome)
	}
	if trial.Cross.Outcome == statusMatched && !sameOffsets(got.ovector, trial.Cross.Ovector) {
		t.Fatalf("trial %d: the backtracking ovector is %v, want %v",
			at, got.ovector, trial.Cross.Ovector)
	}
	if !sameUsage(got.usage, trial.Cross.Usage) {
		t.Fatalf("trial %d: the backtracking usage is %+v, want %+v",
			at, got.usage, trial.Cross.Usage)
	}
	if trial.Cross.Edges {
		sweepEdges(t, sweepBacktrack, re, subject, trial, trial.Cross.Usage, limits, got, at)
	}
}

// Two bounds, or two refusals, for the same configuration and length.
func sameBound(t *testing.T, what string, got sweepBound, want sweepBound, at int) {
	t.Helper()
	for _, which := range []struct {
		name string
		got  *uint64
		want *uint64
	}{
		{"cost", got.Cost, want.Cost},
		{"stack", got.Stack, want.Stack},
		{"mem", got.Mem, want.Mem},
	} {
		if (which.got == nil) != (which.want == nil) {
			t.Fatalf("trial %d: %s %s bound is %v, want %v",
				at, what, which.name, which.got, which.want)
		}
		if which.got != nil && *which.got != *which.want {
			t.Fatalf("trial %d: %s %s bound is %d, want %d",
				at, what, which.name, *which.got, *which.want)
		}
	}
}

// The Pike VM says no to a program compilation did not route to it. There is
// no pair to compare on an ineligible pattern, and the refusal is what is
// worth pinning instead.
func sweepIneligible(t *testing.T, re Re, budget sweepBudget) {
	t.Helper()
	var ov []uint32
	var use Usage
	status := Tir_pike_match(re, nil, 0, 0, budget.Cost, budget.Stack, budget.Memory, &ov, &use)
	if status != statusBadInput {
		t.Fatalf("the Pike VM answered %d for an ineligible program, want BadInput", status)
	}
}

func sweepContextRun(t *testing.T, re Re, one sweepCase, budget sweepBudget) {
	t.Helper()
	// Creation charges one cost unit per IR byte it zeroes, so a cost ceiling
	// equal to the memory one can never be the limit that binds: what a
	// refusal here is about is always the size of the reservation.
	var ctx Ctx
	status := Tir_ctx_create(re, 0, one.Maxlen, budget.Memory, budget.Stack, budget.Memory, &ctx)
	if status != one.Context.Status {
		t.Fatalf("creation answered %d, want %d", status, one.Context.Status)
	}
	if status != 0 {
		return
	}
	if ctx.memcap != one.Context.Memcap {
		t.Fatalf("the context reserves %d, want %d", ctx.memcap, one.Context.Memcap)
	}
	if held := residentTotal(re, &ctx); held != ctx.memcap {
		t.Fatalf("the context holds %d bytes, having reserved %d", held, ctx.memcap)
	}
	sweepCreationEdge(t, re, one, budget)

	var ov []uint32
	var use Usage
	for at, call := range one.Context.Calls {
		trial := one.Trials[at]
		got := Tir_ctx_match(&ctx, sweepBytes(t, trial.Subject), trial.Start, trial.MatchFlags,
			budget.Memory, budget.Stack, &ov, &use)
		if got != call.Outcome {
			t.Fatalf("context call %d answered %d, want %d", at, got, call.Outcome)
		}
		if !sameUsage(use, call.Usage) {
			t.Fatalf("context call %d used %+v, want %+v", at, use, call.Usage)
		}
		// A plain call that ran out of budget is not something a context call
		// has to reproduce: its ceilings are its creation's, and its scratch
		// is already there to be reused rather than grown.
		if trial.Outcome == statusMatched && got == statusMatched {
			if !sameOffsets(sweepOffsets(ov), trial.Ovector) {
				t.Fatalf("context call %d answered %v, the plain call %v",
					at, sweepOffsets(ov), trial.Ovector)
			}
		}
	}
	if one.Context.Edges != nil {
		sweepCallEdges(t, &ctx, one, *one.Context.Edges, budget)
	}
}

func sweepCreationEdge(t *testing.T, re Re, one sweepCase, budget sweepBudget) {
	t.Helper()
	for _, edge := range []struct {
		memory uint64
		want   uint32
	}{{one.Context.Memcap, 0}, {one.Context.Memcap - 1, statusRefused}} {
		var ctx Ctx
		got := Tir_ctx_create(re, 0, one.Maxlen, budget.Memory, budget.Stack, edge.memory, &ctx)
		if got != edge.want {
			t.Fatalf("creation at a memory limit of %d answered %d, want %d",
				edge.memory, got, edge.want)
		}
	}
}

// The per-call cost and stack edges. Memory is not a per-call limit on a
// context — the reservation is made once and a call takes no more — so the
// memory edge is creation's, and it was tested there.
func sweepCallEdges(t *testing.T, ctx *Ctx, one sweepCase, at int, budget sweepBudget) {
	t.Helper()
	trial := one.Trials[at]
	subject := sweepBytes(t, trial.Subject)
	var ov []uint32
	var use Usage
	first := Tir_ctx_match(ctx, subject, trial.Start, trial.MatchFlags,
		budget.Memory, budget.Stack, &ov, &use)
	answer := sweepOffsets(ov)
	observed := use
	for _, dimension := range []string{"cost", "stack"} {
		value := observed.cost
		if dimension == "stack" {
			value = uint64(observed.stack)
		}
		at := func(spent uint64) uint32 {
			cost, stack := budget.Memory, budget.Stack
			if dimension == "cost" {
				cost = spent
			} else {
				stack = uint32(spent)
			}
			return Tir_ctx_match(ctx, subject, trial.Start, trial.MatchFlags,
				cost, stack, &ov, &use)
		}
		if got := at(value); got != first || !sameOffsets(sweepOffsets(ov), answer) {
			t.Fatalf("at the observed %s limit %d a context call answered %d, want %d",
				dimension, value, got, first)
		}
		if value == 0 {
			continue
		}
		if got := at(value - 1); got != statusRefused {
			t.Fatalf("one below the observed %s limit %d a context call answered %d, "+
				"want ResourceExceeded", dimension, value, got)
		}
	}
}

func sweepOne(t *testing.T, one sweepCase, budget sweepBudget) {
	t.Helper()
	re, compiled := sweepCompiled(t, one)
	if !compiled {
		return
	}
	sweepAnalysis(t, re, one)
	if !one.Pike {
		sweepIneligible(t, re, budget)
	}
	for at := range one.Trials {
		sweepTrialRun(t, re, one, at, budget)
	}
	sweepContextRun(t, re, one, budget)
}

func TestSweepShard(t *testing.T) {
	held := sweepLoaded(t)
	budget := *held.Budget
	for _, one := range held.Cases {
		t.Run(one.Family+"-"+strconv.Itoa(one.Index), func(t *testing.T) {
			sweepOne(t, one, budget)
		})
	}
}

// The cases the sweep has actually found and a reducer has shrunk. They are
// kept rather than generated — a generated population is rebuilt from a seed
// and would not find them again once the seed moved on — and they are replayed
// through exactly the same battery, because what each one guards is an
// invariant rather than an answer.
func TestSweepRegressions(t *testing.T) {
	// Possibly empty: a repository that has not found an invariant failure yet
	// has nothing to keep, and a runner that refused an empty section would
	// refuse the shard of a clean checkout. A section that is not there at all
	// is refused by the loader, since that is a sweep this runner would be
	// claiming to have replayed and had not.
	for _, one := range *sweepLoaded(t).Regressions {
		t.Run(one.Name, func(t *testing.T) {
			if one.Budget == nil {
				t.Fatalf("a regression carries no budget of its own")
			}
			sweepOne(t, one, *one.Budget)
		})
	}
}
