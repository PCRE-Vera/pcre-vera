// Code generated from the lowering probe. DO NOT EDIT.
//
// Artifact SHA-256:
//   32df7a0b0f41f6b4594832e9eecccc6714817c19d73733de4662bd0b96d2248a
//
// The lowering probe: a small TIR program that does on purpose what the
// printers can get wrong, with operands sitting on the boundaries. It is
// test material, not part of the library; conformance/lowering.json says
// what every call has to answer.
//
// The package holds the program and the printer's own tir_ helpers and
// nothing else, which is what lets TIR names be printed verbatim.
//
// A tir_ helper panics where TIR-SPEC.md section 12 says a checked operation
// traps. A trap is an engine bug rather than a caller error, so it fails
// loudly instead of reading past the end of an array.

package probe

// ArtifactSHA256 is the SHA-256 of the TIR artifact this package was printed
// from.
const ArtifactSHA256 = "32df7a0b0f41f6b4594832e9eecccc6714817c19d73733de4662bd0b96d2248a"

// Tir_Trap is what a checked operation panics with, per TIR-SPEC.md section 12.
type Tir_Trap struct {
	Code  string
	What  string
	Index uint32
	Bound uint32
}

func (t Tir_Trap) Error() string {
	return "pcretruste: TIR trap " + t.Code + ": " + t.What
}

const tir_CAP uint64 = 9007199254740991

const tir_fellOff = "pcretruste: a value-returning function reached its end"

func tir_oob(index uint32, bound uint32) {
	panic(Tir_Trap{Code: "T-01", What: "index past the end of a sequence", Index: index, Bound: bound})
}

// tir_k is the identity. It stands between a literal and an operator whose Go
// constant form would refuse to wrap, and it costs nothing once inlined.
func tir_k[T any](x T) T { return x }

func tir_b(x bool) uint64 {
	if x {
		return 1
	}
	return 0
}

// tir_c is the i32-to-counter cast: a count has no negative reading, so a
// negative operand lands at zero rather than being reinterpreted.
func tir_c(x int32) uint64 {
	if x < 0 {
		return 0
	}
	return uint64(x)
}

// The three counter operators of TIR-SPEC.md section 6.7, checked before the
// arithmetic rather than clamped after it.
func tir_cadd(a uint64, b uint64) uint64 {
	if a > tir_CAP-b {
		return tir_CAP
	}
	return a + b
}

func tir_csub(a uint64, b uint64) uint64 {
	if a < b {
		return 0
	}
	return a - b
}

func tir_cmul(a uint64, b uint64) uint64 {
	if a == 0 || b == 0 {
		return 0
	}
	if a > tir_CAP/b {
		return tir_CAP
	}
	return a * b
}

// Division and remainder, with a zero divisor answered by the fallback and the
// two i32 corners that would otherwise be a runtime panic.
func tir_div_u8(a uint8, b uint8, f uint8) uint8 {
	if b == 0 {
		return f
	}
	return a / b
}

func tir_rem_u8(a uint8, b uint8, f uint8) uint8 {
	if b == 0 {
		return f
	}
	return a % b
}

func tir_div_u32(a uint32, b uint32, f uint32) uint32 {
	if b == 0 {
		return f
	}
	return a / b
}

func tir_rem_u32(a uint32, b uint32, f uint32) uint32 {
	if b == 0 {
		return f
	}
	return a % b
}

func tir_div_counter(a uint64, b uint64, f uint64) uint64 {
	if b == 0 {
		return f
	}
	return a / b
}

func tir_rem_counter(a uint64, b uint64, f uint64) uint64 {
	if b == 0 {
		return f
	}
	return a % b
}

func tir_div_i32(a int32, b int32, f int32) int32 {
	if b == 0 {
		return f
	}
	if b == -1 {
		return -a
	}
	return a / b
}

func tir_rem_i32(a int32, b int32, f int32) int32 {
	if b == 0 {
		return f
	}
	if b == -1 {
		return 0
	}
	return a % b
}

// Sequences. A Go slice already carries the two numbers the growth schedule of
// TIR-SPEC.md section 11 talks about: len is the TIR length and cap the TIR
// capacity. Every allocation goes through tir_grow, which copies into a fresh
// buffer rather than reallocating in place, because the memory accounting
// counts both buffers as live at once.
func tir_grow[T any](s []T, capacity int) []T {
	grown := make([]T, len(s), capacity)
	copy(grown, s)
	return grown
}

func tir_push[T any](s *[]T, limit int, v T) {
	n := len(*s)
	if n >= limit {
		panic(Tir_Trap{Code: "T-05", What: "push past the declared maximum", Index: uint32(n), Bound: uint32(limit)})
	}
	if n == cap(*s) {
		capacity := 2 * cap(*s)
		if capacity < 4 {
			capacity = 4
		}
		if capacity > limit {
			capacity = limit
		}
		*s = tir_grow(*s, capacity)
	}
	*s = (*s)[:n+1]
	(*s)[n] = v
}

func tir_pop[T any](s *[]T) T {
	n := len(*s)
	if n == 0 {
		panic(Tir_Trap{Code: "T-02", What: "pop from an empty sequence", Index: 0, Bound: 0})
	}
	v := (*s)[n-1]
	*s = (*s)[:n-1]
	return v
}

func tir_truncate[T any](s *[]T, length uint32) {
	if uint64(length) > uint64(len(*s)) {
		panic(Tir_Trap{Code: "T-03", What: "truncate past the current length", Index: length, Bound: uint32(len(*s))})
	}
	*s = (*s)[:length]
}

func tir_reserve[T any](s *[]T, capacity uint32, limit int) {
	if uint64(capacity) > uint64(limit) {
		panic(Tir_Trap{Code: "T-04", What: "reserve past the declared maximum", Index: capacity, Bound: uint32(limit)})
	}
	if uint64(capacity) > uint64(cap(*s)) {
		*s = tir_grow(*s, int(capacity))
	}
}

type Colour int32

const Red Colour = 0
const Green Colour = 1
const Blue Colour = 2

type Nest struct {
	pair Pair
	tag uint32
}

type Pair struct {
	lo uint32
	hi uint32
}

const BIGB uint8 = 200

const BIGC uint64 = 9007199254740991

const BIGI int32 = -2000000009

const BIGU uint32 = 4000000007

const MINI int32 = -2147483648

var TABLE = []byte{
	0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
	0x1c, 0x1d, 0x1e, 0x1f,
}

func bump(slot *uint32, by uint32) {
	(*slot) = ((*slot) + by)
}

func probe(kind uint32, a uint64, b uint64) uint64 {
	var au uint32 = uint32(a)
	var bu uint32 = uint32(b)
	var ai int32 = int32(a)
	var bi int32 = int32(b)
	var a8 uint8 = uint8(a)
	var b8 uint8 = uint8(b)
	if (kind == uint32(0)) {
		return uint64((au * bu))
	}
	if (kind == uint32(1)) {
		return uint64((au + bu))
	}
	if (kind == uint32(2)) {
		return uint64((au - bu))
	}
	if (kind == uint32(3)) {
		return uint64((au & bu))
	}
	if (kind == uint32(4)) {
		return uint64((au | bu))
	}
	if (kind == uint32(5)) {
		return uint64((au ^ bu))
	}
	if (kind == uint32(6)) {
		return uint64((-au))
	}
	if (kind == uint32(7)) {
		return uint64((^au))
	}
	if (kind == uint32(8)) {
		return uint64((au << 17))
	}
	if (kind == uint32(9)) {
		return uint64((au >> 17))
	}
	if (kind == uint32(10)) {
		return uint64(tir_div_u32(au, bu, uint32(4242)))
	}
	if (kind == uint32(11)) {
		return uint64(tir_rem_u32(au, bu, uint32(4242)))
	}
	if (kind == uint32(12)) {
		return uint64(uint32((ai * bi)))
	}
	if (kind == uint32(13)) {
		return uint64(uint32((ai + bi)))
	}
	if (kind == uint32(14)) {
		return uint64(uint32((ai - bi)))
	}
	if (kind == uint32(15)) {
		return uint64(uint32((-ai)))
	}
	if (kind == uint32(16)) {
		return uint64(uint32((ai >> 5)))
	}
	if (kind == uint32(17)) {
		return uint64(uint32((ai << 5)))
	}
	if (kind == uint32(18)) {
		return uint64(uint32(tir_div_i32(ai, bi, int32(-4242))))
	}
	if (kind == uint32(19)) {
		return uint64(uint32(tir_rem_i32(ai, bi, int32(-4242))))
	}
	if (kind == uint32(20)) {
		return uint64((a8 * b8))
	}
	if (kind == uint32(21)) {
		return uint64((a8 + b8))
	}
	if (kind == uint32(22)) {
		return uint64((a8 - b8))
	}
	if (kind == uint32(23)) {
		return uint64((-a8))
	}
	if (kind == uint32(24)) {
		return uint64((^a8))
	}
	if (kind == uint32(25)) {
		return uint64((a8 << 5))
	}
	if (kind == uint32(26)) {
		return uint64((a8 >> 3))
	}
	if (kind == uint32(27)) {
		return tir_cadd(a, b)
	}
	if (kind == uint32(28)) {
		return tir_csub(a, b)
	}
	if (kind == uint32(29)) {
		return tir_cmul(a, b)
	}
	if (kind == uint32(30)) {
		return tir_div_counter(a, b, uint64(4242))
	}
	if (kind == uint32(31)) {
		return tir_rem_counter(a, b, uint64(4242))
	}
	if (kind == uint32(32)) {
		return uint64(uint8(a))
	}
	if (kind == uint32(33)) {
		return uint64(uint32(a))
	}
	if (kind == uint32(34)) {
		return uint64(uint32(int32(a)))
	}
	if (kind == uint32(35)) {
		return tir_c(ai)
	}
	if (kind == uint32(36)) {
		return uint64(uint8(ai))
	}
	if (kind == uint32(37)) {
		return tir_b((au < bu))
	}
	if (kind == uint32(38)) {
		var push_bag []uint32
		var push_i uint32 = uint32(0)
		for (push_i < au) {
			tir_push(&push_bag, 40, push_i)
			push_i = (push_i + uint32(1))
		}
		return tir_cadd(tir_cmul(uint64(uint32(cap(push_bag))), uint64(16777216)), uint64(uint32(len(push_bag))))
	}
	if (kind == uint32(39)) {
		var res_bag []uint32
		tir_reserve(&res_bag, bu, 40)
		var res_i uint32 = uint32(0)
		for (res_i < au) {
			tir_push(&res_bag, 40, res_i)
			res_i = (res_i + uint32(1))
		}
		return tir_cadd(tir_cmul(uint64(uint32(cap(res_bag))), uint64(16777216)), uint64(uint32(len(res_bag))))
	}
	if (kind == uint32(40)) {
		var trunc_bag []uint32
		var trunc_i uint32 = uint32(0)
		for (trunc_i < au) {
			tir_push(&trunc_bag, 40, trunc_i)
			trunc_i = (trunc_i + uint32(1))
		}
		tir_truncate(&trunc_bag, bu)
		return tir_cadd(tir_cmul(uint64(uint32(cap(trunc_bag))), uint64(16777216)), uint64(uint32(len(trunc_bag))))
	}
	if (kind == uint32(41)) {
		var pop_bag []uint32
		var pop_i uint32 = uint32(0)
		for (pop_i < au) {
			tir_push(&pop_bag, 40, (pop_i + uint32(100)))
			pop_i = (pop_i + uint32(1))
		}
		var pop_last uint32 = uint32(0)
		pop_last = tir_pop(&pop_bag)
		return tir_cadd(tir_cmul(uint64(pop_last), uint64(16777216)), uint64(uint32(len(pop_bag))))
	}
	if (kind == uint32(42)) {
		var copy_from []uint32
		tir_push(&copy_from, 40, au)
		tir_push(&copy_from, 40, bu)
		var copy_to []uint32
		copy_to = tir_copy_vec_u32_40(copy_from)
		tir_t1 := uint32(0)
		if tir_t1 >= uint32(len(copy_from)) {
			tir_oob(tir_t1, uint32(len(copy_from)))
		}
		copy_from[tir_t1] = uint32(777)
		return tir_cadd(tir_cmul(uint64(copy_to[uint32(0)]), uint64(16777216)), uint64(uint32(cap(copy_to))))
	}
	if (kind == uint32(43)) {
		var freeze_from []uint32
		tir_push(&freeze_from, 40, au)
		var freeze_to []uint32
		freeze_to = freeze_from
		freeze_from = nil
		return tir_cadd(tir_cmul(uint64(freeze_to[uint32(0)]), uint64(16777216)), uint64(uint32(len(freeze_from))))
	}
	if (kind == uint32(44)) {
		return uint64(TABLE[(au & uint32(15))])
	}
	if (kind == uint32(45)) {
		var sc_bag []uint32
		tir_push(&sc_bag, 40, uint32(7))
		return tir_b(((au < uint32(len(sc_bag))) && (sc_bag[au] == uint32(7))))
	}
	if (kind == uint32(46)) {
		var sr_first Pair = (Pair{lo: au, hi: bu})
		var sr_second Pair = sr_first
		sr_second.lo = uint32(777)
		return tir_cadd(tir_cmul(uint64(sr_first.lo), uint64(16777216)), uint64(sr_second.lo))
	}
	if (kind == uint32(47)) {
		var er_bag []Pair
		tir_push(&er_bag, 8, (Pair{lo: au, hi: bu}))
		var er_held Pair = er_bag[uint32(0)]
		er_held.lo = uint32(777)
		return tir_cadd(tir_cmul(uint64(er_bag[uint32(0)].lo), uint64(16777216)), uint64(er_held.lo))
	}
	if (kind == uint32(48)) {
		var nf_outer Nest = (Nest{pair: (Pair{lo: au, hi: bu}), tag: uint32(1)})
		var nf_held Pair = nf_outer.pair
		nf_held.lo = uint32(777)
		return tir_cadd(tir_cmul(uint64(nf_outer.pair.lo), uint64(16777216)), uint64(nf_held.lo))
	}
	if (kind == uint32(49)) {
		var ew_bag []Pair
		tir_push(&ew_bag, 8, (Pair{lo: au, hi: bu}))
		tir_t2 := uint32(0)
		if tir_t2 >= uint32(len(ew_bag)) {
			tir_oob(tir_t2, uint32(len(ew_bag)))
		}
		ew_bag[tir_t2].lo = uint32(777)
		return tir_cadd(tir_cmul(uint64(ew_bag[uint32(0)].lo), uint64(16777216)), uint64(ew_bag[uint32(0)].hi))
	}
	if (kind == uint32(50)) {
		var il_held uint32 = au
		bump(&il_held, bu)
		return uint64(il_held)
	}
	if (kind == uint32(51)) {
		var ie_bag []uint32
		tir_push(&ie_bag, 40, au)
		tir_t3 := uint32(0)
		if tir_t3 >= uint32(len(ie_bag)) {
			tir_oob(tir_t3, uint32(len(ie_bag)))
		}
		bump(&ie_bag[tir_t3], bu)
		return uint64(ie_bag[uint32(0)])
	}
	if (kind == uint32(52)) {
		var if_held Pair = (Pair{lo: au, hi: uint32(0)})
		bump(&if_held.lo, bu)
		return tir_cadd(tir_cmul(uint64(if_held.lo), uint64(16777216)), uint64(if_held.hi))
	}
	if (kind == uint32(53)) {
		var is_held Pair = (Pair{lo: au, hi: bu})
		swap_pair(&is_held)
		return tir_cadd(tir_cmul(uint64(is_held.lo), uint64(16777216)), uint64(is_held.hi))
	}
	if (kind == uint32(54)) {
		var vb_bag []bool
		tir_push(&vb_bag, 40, (au < bu))
		tir_push(&vb_bag, 40, (au > bu))
		return tir_cadd(tir_cmul(uint64(uint32(tir_b(vb_bag[uint32(0)]))), uint64(16777216)), uint64(uint32(tir_b(vb_bag[uint32(1)]))))
	}
	if (kind == uint32(55)) {
		var v8_bag []uint8
		tir_push(&v8_bag, 40, a8)
		tir_push(&v8_bag, 40, b8)
		return tir_cadd(tir_cmul(uint64(uint32(v8_bag[uint32(0)])), uint64(16777216)), uint64(uint32(v8_bag[uint32(1)])))
	}
	if (kind == uint32(56)) {
		var vi_bag []int32
		tir_push(&vi_bag, 40, ai)
		tir_push(&vi_bag, 40, bi)
		return tir_cadd(tir_cmul(uint64(uint32(vi_bag[uint32(0)])), uint64(16777216)), uint64(uint32(vi_bag[uint32(1)])))
	}
	if (kind == uint32(57)) {
		var vc_bag []uint64
		tir_push(&vc_bag, 40, a)
		tir_push(&vc_bag, 40, b)
		return tir_cadd(vc_bag[uint32(0)], vc_bag[uint32(1)])
	}
	if (kind == uint32(58)) {
		var ve_bag []Colour
		tir_push(&ve_bag, 40, Green)
		tir_push(&ve_bag, 40, Blue)
		return tir_cadd(tir_cmul(uint64(uint32(tir_b((ve_bag[uint32(0)] == Green)))), uint64(16777216)), uint64(uint32(tir_b((ve_bag[uint32(1)] == Blue)))))
	}
	if (kind == uint32(59)) {
		var vf_bag [][]byte
		tir_push(&vf_bag, 8, TABLE)
		return tir_cadd(tir_cmul(uint64(uint32(len(vf_bag[uint32(0)]))), uint64(16777216)), uint64(uint32(vf_bag[uint32(0)][(au & uint32(15))])))
	}
	if (kind == uint32(60)) {
		var sc_picked Colour
		if (au == uint32(0)) {
			sc_picked = Red
		} else {
			if (au == uint32(1)) {
				sc_picked = Green
			} else {
				sc_picked = Blue
			}
		}
		var sc_answer uint32 = uint32(0)
		switch sc_picked {
		case Red:
			sc_answer = uint32(10)
		case Green:
			sc_answer = uint32(20)
		case Blue:
			sc_answer = uint32(30)
		}
		return uint64(sc_answer)
	}
	if (kind == uint32(61)) {
		var sd_picked Colour
		if (au == uint32(1)) {
			sd_picked = Green
		}
		var sd_answer uint32 = uint32(7)
		switch sd_picked {
		case Green:
		default:
			sd_answer = uint32(99)
		}
		return uint64(sd_answer)
	}
	if (kind == uint32(62)) {
		var bs_i uint32 = uint32(0)
		var bs_total uint32 = uint32(0)
		tir_loop1:
		for (bs_i < uint32(40)) {
			var bs_picked Colour
			if (bs_i == au) {
				bs_picked = Red
			} else {
				bs_picked = Green
			}
			switch bs_picked {
			case Red:
				break tir_loop1
			default:
				bs_total = (bs_total + uint32(1))
			}
			bs_i = (bs_i + uint32(1))
		}
		return tir_cadd(tir_cmul(uint64(bs_i), uint64(16777216)), uint64(bs_total))
	}
	if (kind == uint32(63)) {
		var ts_left uint32 = au
		var ts_right uint32 = bu
		_ = ts_right
		tir_t4 := ts_left
		ts_left = ts_right
		ts_right = tir_t4
		var ts_emptied uint32 = uint32(0)
		ts_emptied = ts_left
		ts_left = uint32(0)
		return tir_cadd(tir_cmul(uint64(ts_emptied), uint64(16777216)), uint64(ts_left))
	}
	if (kind == uint32(64)) {
		return uint64(tir_k((tir_k(BIGU) + uint32(4000000007))))
	}
	if (kind == uint32(65)) {
		return uint64(tir_k((tir_k(BIGU) + BIGU)))
	}
	if (kind == uint32(66)) {
		return uint64(tir_k((-tir_k(BIGU))))
	}
	if (kind == uint32(67)) {
		return uint64(tir_k((tir_k(BIGU) << 5)))
	}
	if (kind == uint32(68)) {
		return uint64(tir_k(uint8(tir_k(BIGU))))
	}
	if (kind == uint32(69)) {
		return uint64(tir_k(uint32(tir_k((tir_k(BIGI) + BIGI)))))
	}
	if (kind == uint32(70)) {
		return uint64(tir_k(uint32(tir_k((-tir_k(MINI))))))
	}
	if (kind == uint32(71)) {
		return uint64(tir_k((tir_k(BIGB) + BIGB)))
	}
	if (kind == uint32(72)) {
		return uint64(tir_k(uint32(tir_k(BIGC))))
	}
	return uint64(0)
}

func swap_pair(p *Pair) {
	var held uint32 = (*p).lo
	(*p).lo = (*p).hi
	(*p).hi = held
}

func tir_copy_vec_u32_40(s []uint32) []uint32 {
	d := make([]uint32, len(s), len(s))
	for i := range s {
		d[i] = tir_copy_u32(s[i])
	}
	return d
}

func tir_copy_u32(s uint32) uint32 {
	return s
}

// The exported façade. Go cannot reach a lower-case name from another
// package and TIR names are printed verbatim, so the wrapper next door
// talks to the program through these. They add no behaviour of their own.

func Tir_bump(slot *uint32, by uint32) {
	bump(slot, by)
}

func Tir_probe(kind uint32, a uint64, b uint64) uint64 {
	return probe(kind, a, b)
}

func Tir_swap_pair(p *Pair) {
	swap_pair(p)
}

func (v *Nest) Tir_pair() Pair { return v.pair }
func (v *Nest) Tir_tag() uint32 { return v.tag }

func (v *Pair) Tir_lo() uint32 { return v.lo }
func (v *Pair) Tir_hi() uint32 { return v.hi }
