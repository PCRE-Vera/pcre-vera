package engine

// The physical half of the context contract, asked where the arrays are
// visible: the capacities a created context really holds, weighed at the IR
// sizes of BOUNDS.md section 3, sum to the memory bound — together with the
// wrapper-owned ovector, whose share is the setup term's novec slots. The
// corpus pins the same number through the public wrapper; this is the check
// that the number is made of real bytes rather than reported.

import (
	"encoding/hex"
	"testing"
)

func residentBytes(ctx *Ctx) uint64 {
	return uint64(cap(ctx.regs))*4 +
		uint64(cap(ctx.bt))*12 +
		uint64(cap(ctx.trail))*8 +
		uint64(cap(ctx.clist))*8 +
		uint64(cap(ctx.nlist))*8 +
		uint64(cap(ctx.stk))*8 +
		uint64(cap(ctx.seen)) +
		uint64(cap(ctx.rc))*4 +
		uint64(cap(ctx.free))*4 +
		uint64(cap(ctx.pool))*4 +
		uint64(cap(ctx.slack))
}

// Everything a context reserved, the arrays plus the two result stores the
// wrapper materializes beside it: the engine ovector the run cores fill, and
// the converted view a match answers through. One statement of the sum, since
// both runners in this package ask for it.
func residentTotal(re Re, ctx *Ctx) uint64 {
	return residentBytes(ctx) + uint64(2*(re.ncap+1))*4*2
}

func TestAContextIsTheMemoryBoundMadePhysical(t *testing.T) {
	for _, tc := range []struct {
		pattern string
		maxlen  uint32
	}{
		{"abc", 64},
		{"(a)(b*)", 64},
		{"a*", 0},
		{"a{1,2}", 16},
		{"a{0,2}b*", 32},
		{"(ab)*c", 100},
	} {
		re := buildProgram(t, hex.EncodeToString([]byte(tc.pattern)))
		var ctx Ctx
		status := Tir_ctx_create(re, 0, tc.maxlen, 1<<40, 100_000, 1<<31-1, &ctx)
		if status != 0 {
			t.Fatalf("%s: creation answered %d", tc.pattern, status)
		}
		if got := residentTotal(re, &ctx); got != ctx.memcap {
			t.Fatalf(
				"%s at %d: %d resident bytes against a reservation of %d",
				tc.pattern, tc.maxlen, got, ctx.memcap,
			)
		}
		bound := Tir_re_mem(re, 0, uint64(tc.maxlen))
		if bound.status != 0 || bound.value != ctx.memcap {
			t.Fatalf(
				"%s at %d: the reservation is %d, the accessor answers %v",
				tc.pattern, tc.maxlen, ctx.memcap, bound,
			)
		}
	}
}
