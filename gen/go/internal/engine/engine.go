// Code generated from engine.tir.json. DO NOT EDIT.
//
// Artifact SHA-256:
//   6a6dfaddef328fdb85950946041356ab3a55a766835ab415dc7d764d02569451
//
// The wave 1 pcre-vera engine as printed from its TIR artifact: the pattern
// parser, the bytecode compiler, and the backtracking matcher. The public
// API lives in the package next door.
//
// The package holds the program and the printer's own tir_ helpers and
// nothing else, which is what lets TIR names be printed verbatim.
//
// A tir_ helper panics where TIR-SPEC.md section 12 says a checked operation
// traps. A trap is an engine bug rather than a caller error, so it fails
// loudly instead of reading past the end of an array.

package engine

// ArtifactSHA256 is the SHA-256 of the TIR artifact this package was printed
// from.
const ArtifactSHA256 = "6a6dfaddef328fdb85950946041356ab3a55a766835ab415dc7d764d02569451"

// Tir_Trap is what a checked operation panics with, per TIR-SPEC.md section 12.
type Tir_Trap struct {
	Code  string
	What  string
	Index uint32
	Bound uint32
}

func (t Tir_Trap) Error() string {
	return "pcrevera: TIR trap " + t.Code + ": " + t.What
}

const tir_CAP uint64 = 9007199254740991

const tir_fellOff = "pcrevera: a value-returning function reached its end"

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

type Ar int32

const ArShape Ar = 0
const ArAmbiguous Ar = 1
const ArOverflow Ar = 2
const ArOk Ar = 3

type Bk int32

const BkCost Bk = 0
const BkStack Bk = 1
const BkMem Bk = 2

type Cc int32

const CcNotProvenLinear Cc = 0
const CcLinear Cc = 1

type Cfg int32

const CfgBacktrack Cfg = 0
const CfgPike Cfg = 1
const CfgMemo Cfg = 2

type Cr int32

const CrNoRegions Cr = 0
const CrRootKind Cr = 1
const CrRootParent Cr = 2
const CrRootRange Cr = 3
const CrTwoRoots Cr = 4
const CrParentOrder Cr = 5
const CrBackwards Cr = 6
const CrNotNested Cr = 7
const CrOverlap Cr = 8
const CrNoRules Cr = 9
const CrConfig Cr = 10
const CrIneligible Cr = 11
const CrPrices Cr = 12
const CrBase Cr = 13
const CrOpcode Cr = 14
const CrShape Cr = 15
const CrChildren Cr = 16
const CrAmbiguous Cr = 17
const CrOverflow Cr = 18
const CrRegionWork Cr = 19
const CrRegionOuts Cr = 20
const CrRegionStack Cr = 21
const CrRegionTrail Cr = 22
const CrTotalCost Cr = 23
const CrTotalStack Cr = 24
const CrTotalTrail Cr = 25
const CrTotalMem Cr = 26
const CrNotLinear Cr = 27
const CrOk Cr = 28

type Ek int32

const EkErr Ek = 0
const EkChar Ek = 1
const EkSet Ek = 2
const EkNegSet Ek = 3
const EkSod Ek = 4
const EkEod Ek = 5
const EkEodn Ek = 6
const EkWordB Ek = 7
const EkNotWordB Ek = 8
const EkBsr Ek = 9
const EkNop Ek = 10

type Nd int32

const NdNil Nd = 0
const NdChar Nd = 1
const NdCharCI Nd = 2
const NdClass Nd = 3
const NdAny Nd = 4
const NdAnyNoNL Nd = 5
const NdBsr Nd = 6
const NdConcat Nd = 7
const NdAlt Nd = 8
const NdGroup Nd = 9
const NdRepeat Nd = 10
const NdCirc Nd = 11
const NdCircM Nd = 12
const NdDoll Nd = 13
const NdDollE Nd = 14
const NdDollM Nd = 15
const NdSod Nd = 16
const NdEod Nd = 17
const NdEodn Nd = 18
const NdWordB Nd = 19
const NdNotWordB Nd = 20

type Op int32

const OpChar Op = 0
const OpCharCI Op = 1
const OpClass Op = 2
const OpAny Op = 3
const OpAnyNoNL Op = 4
const OpBsr Op = 5
const OpSplit Op = 6
const OpJump Op = 7
const OpSave Op = 8
const OpCirc Op = 9
const OpCircM Op = 10
const OpDoll Op = 11
const OpDollE Op = 12
const OpDollM Op = 13
const OpSod Op = 14
const OpEod Op = 15
const OpEodn Op = 16
const OpWordB Op = 17
const OpNotWordB Op = 18
const OpRepZero Op = 19
const OpRepLoop Op = 20
const OpRepEnter Op = 21
const OpRepNext Op = 22
const OpAccept Op = 23

type Rk int32

const RkRoot Rk = 0
const RkGroup Rk = 1
const RkBranch Rk = 2
const RkAlt Rk = 3
const RkRepeat Rk = 4

type Acc struct {
	work Poly
	stack Poly
	trail Poly
	flow Poly
}

type Answer struct {
	status uint32
	value uint64
}

type Bound struct {
	ok bool
	value uint64
}

type Bt struct {
	pc uint32
	pos uint32
	mark uint32
}

type Cert struct {
	config Cfg
	complexity Cc
	cost Poly
	stack Poly
	trail Poly
	mem Poly
	prices []Price
}

type Ctx struct {
	re Re
	ready bool
	maxlen uint32
	costcap uint64
	stackcap uint32
	memcap uint64
	regs []uint32
	bt []Bt
	trail []Undo
	clist []Th
	nlist []Th
	stk []Th
	seen []byte
	pool []uint32
	rc []uint32
	free []uint32
	slack []byte
}

type Esc struct {
	kind Ek
	val uint32
}

type Frame struct {
	grp uint32
	alt uint32
	cat uint32
	qual uint32
	opts uint32
	at uint32
	unsup uint32
}

type Inst struct {
	op Op
	arg uint32
	alt uint32
}

type Job struct {
	node uint32
	phase uint32
	cur uint32
	mark uint32
	base uint32
	here uint32
	arm uint32
}

type NameEnt struct {
	off uint32
	nlen uint32
	grp uint32
}

type Node struct {
	kind Nd
	val uint32
	aux uint32
	opts uint32
	first uint32
	last uint32
	nxt uint32
}

type Out struct {
	err uint32
	erroff uint32
	re Re
}

type Poly struct {
	base uint64
	c0 uint64
	c1 uint64
	c2 uint64
	c3 uint64
	c4 uint64
}

type Price struct {
	work Poly
	outs Poly
	stack Poly
	trail Poly
}

type Quant struct {
	ok bool
	lo uint32
	hi uint32
	end uint32
}

type Re struct {
	code []Inst
	classes []byte
	reps []Rep
	regions []Region
	names []byte
	nameents []NameEnt
	ncap uint32
	nname uint32
	nregs uint32
	opts uint32
	nltype uint32
	bsr uint32
	hascrlf uint32
	crfirst uint32
	pike bool
	hascert bool
	cert Cert
	haspikecert bool
	pikecert Cert
}

type Ref struct {
	num uint32
	off uint32
	nlen uint32
}

type Region struct {
	kind Rk
	parent uint32
	lo uint32
	hi uint32
}

type Rep struct {
	lo uint32
	hi uint32
	greedy bool
	head uint32
	body uint32
	after uint32
}

type Room struct {
	lists uint64
	stk uint64
	tables uint64
	pool uint64
	words uint32
	reserved uint64
}

type Th struct {
	pc uint32
	h uint32
}

type Undo struct {
	slot uint32
	old uint32
}

type Usage struct {
	cost uint64
	stack uint32
	mem uint64
}

type Work struct {
	nodes []Node
	frames []Frame
	classes []byte
	names []byte
	nameents []NameEnt
	code []Inst
	reps []Rep
	regions []Region
	jobs []Job
	patches []uint32
	ncap uint32
	nname uint32
	nclass uint32
	nrep uint32
	opts uint32
	err uint32
	erroff uint32
	root uint32
	refs []Ref
	hascrlf uint32
	crfirst uint32
	nltype uint32
	clselems uint32
	clsrange uint32
	clscrlf uint32
	pending []uint32
	seen []byte
}

var BITS = []byte{
	0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80,
}

var CTYPE = []byte{
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x02, 0x02,
	0x02, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x0d, 0x0d, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x29, 0x29, 0x29, 0x29, 0x29, 0x29, 0x21,
	0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21,
	0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x00, 0x00, 0x00, 0x00, 0x01,
	0x00, 0x29, 0x29, 0x29, 0x29, 0x29, 0x29, 0x21, 0x21, 0x21, 0x21, 0x21,
	0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21, 0x21,
	0x21, 0x21, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00,
}

var FLIP = []byte{
	0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
	0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
	0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23,
	0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
	0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b,
	0x3c, 0x3d, 0x3e, 0x3f, 0x40, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,
	0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73,
	0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
	0x60, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b,
	0x4c, 0x4d, 0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
	0x58, 0x59, 0x5a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f, 0x80, 0x81, 0x82, 0x83,
	0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
	0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
	0x9c, 0x9d, 0x9e, 0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
	0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3,
	0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
	0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xcb,
	0xcc, 0xcd, 0xce, 0xcf, 0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7,
	0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf, 0xe0, 0xe1, 0xe2, 0xe3,
	0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef,
	0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
	0xfc, 0xfd, 0xfe, 0xff,
}

var LOWER = []byte{
	0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
	0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
	0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23,
	0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
	0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b,
	0x3c, 0x3d, 0x3e, 0x3f, 0x40, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,
	0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73,
	0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
	0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b,
	0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
	0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f, 0x80, 0x81, 0x82, 0x83,
	0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
	0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
	0x9c, 0x9d, 0x9e, 0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
	0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3,
	0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
	0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xcb,
	0xcc, 0xcd, 0xce, 0xcf, 0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7,
	0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf, 0xe0, 0xe1, 0xe2, 0xe3,
	0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef,
	0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
	0xfc, 0xfd, 0xfe, 0xff,
}

var POSIX = []byte{
	0x05, 0x61, 0x6c, 0x6e, 0x75, 0x6d, 0x06, 0x05, 0x61, 0x6c, 0x70, 0x68,
	0x61, 0x05, 0x05, 0x61, 0x73, 0x63, 0x69, 0x69, 0x07, 0x05, 0x62, 0x6c,
	0x61, 0x6e, 0x6b, 0x08, 0x05, 0x63, 0x6e, 0x74, 0x72, 0x6c, 0x09, 0x05,
	0x64, 0x69, 0x67, 0x69, 0x74, 0x00, 0x05, 0x67, 0x72, 0x61, 0x70, 0x68,
	0x0a, 0x05, 0x6c, 0x6f, 0x77, 0x65, 0x72, 0x0b, 0x05, 0x70, 0x72, 0x69,
	0x6e, 0x74, 0x0c, 0x05, 0x70, 0x75, 0x6e, 0x63, 0x74, 0x0d, 0x05, 0x73,
	0x70, 0x61, 0x63, 0x65, 0x02, 0x05, 0x75, 0x70, 0x70, 0x65, 0x72, 0x0e,
	0x04, 0x77, 0x6f, 0x72, 0x64, 0x01, 0x06, 0x78, 0x64, 0x69, 0x67, 0x69,
	0x74, 0x0f,
}

var SETS = []byte{
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x03, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0xff, 0x03, 0xfe, 0xff, 0xff, 0x87, 0xfe, 0xff, 0xff, 0x07,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x3e, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3c, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0xfe, 0xff, 0xff, 0x07, 0xfe, 0xff, 0xff, 0x07, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x03, 0xfe, 0xff, 0xff, 0x07,
	0xfe, 0xff, 0xff, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0xfe, 0xff, 0xff, 0x07, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0x7f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0xfe, 0xff, 0x00, 0xfc, 0x01, 0x00, 0x00, 0xf8, 0x01, 0x00, 0x00, 0x78,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0xfe, 0xff, 0xff, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x03, 0x7e, 0x00, 0x00, 0x00,
	0x7e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
}

func add_char(w *Work, c uint32) {
	var tmp1 Nd = NdChar
	var tmp2 uint32 = c
	if ((c == uint32(10)) || (c == uint32(13))) {
		(*w).hascrlf = uint32(1)
	}
	if (((*w).opts & uint32(1)) != uint32(0)) {
		if (FLIP[c] != uint8(c)) {
			tmp1 = NdCharCI
			tmp2 = uint32(LOWER[c])
		}
	}
	attach_atom(w, tmp1, tmp2, uint32(0))
}

func add_child(w *Work, parent uint32, child uint32) {
	if ((*w).nodes[parent].first == uint32(0)) {
		tir_t1 := parent
		if tir_t1 >= uint32(len((*w).nodes)) {
			tir_oob(tir_t1, uint32(len((*w).nodes)))
		}
		(*w).nodes[tir_t1].first = child
	} else {
		var tmp1 uint32 = (*w).nodes[parent].last
		tir_t2 := tmp1
		if tir_t2 >= uint32(len((*w).nodes)) {
			tir_oob(tir_t2, uint32(len((*w).nodes)))
		}
		(*w).nodes[tir_t2].nxt = child
	}
	tir_t3 := parent
	if tir_t3 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t3, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t3].last = child
}

func alloc_node(w *Work, kind Nd, val uint32, aux uint32, nopts uint32) uint32 {
	var tmp1 uint32 = uint32(len((*w).nodes))
	if (tmp1 >= uint32(8208)) {
		(*w).err = uint32(1002)
		return uint32(0)
	}
	tir_push(&(*w).nodes, 8208, (Node{kind: kind, val: val, aux: aux, opts: nopts, first: uint32(0), last: uint32(0), nxt: uint32(0)}))
	return tmp1
}

func apply_quant(w *Work, lo uint32, hi uint32, greedy bool, erroff uint32) {
	var tmp1 uint32 = (uint32(len((*w).frames)) - uint32(1))
	var tmp2 uint32 = (*w).frames[tmp1].qual
	if (tmp2 == uint32(0)) {
		(*w).err = uint32(109)
		(*w).erroff = erroff
		return
	}
	var tmp3 Nd = (*w).nodes[tmp2].kind
	var tmp4 bool = true
	switch tmp3 {
	case NdRepeat:
		tmp4 = false
	case NdCirc:
		tmp4 = false
	case NdCircM:
		tmp4 = false
	case NdDoll:
		tmp4 = false
	case NdDollE:
		tmp4 = false
	case NdDollM:
		tmp4 = false
	case NdSod:
		tmp4 = false
	case NdEod:
		tmp4 = false
	case NdEodn:
		tmp4 = false
	case NdWordB:
		tmp4 = false
	case NdNotWordB:
		tmp4 = false
	default:
	}
	if (!tmp4) {
		(*w).err = uint32(109)
		(*w).erroff = erroff
		return
	}
	var tmp5 uint32 = uint32(0)
	var tmp6 Node = (*w).nodes[tmp2]
	tir_t1 := alloc_node(w, tmp6.kind, tmp6.val, tmp6.aux, tmp6.opts)
	tmp5 = tir_t1
	if ((*w).err != uint32(0)) {
		return
	}
	tir_t2 := tmp5
	if tir_t2 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t2, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t2].first = tmp6.first
	tir_t3 := tmp5
	if tir_t3 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t3, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t3].last = tmp6.last
	tir_t4 := tmp2
	if tir_t4 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t4, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t4].kind = NdRepeat
	tir_t5 := tmp2
	if tir_t5 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t5, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t5].val = lo
	tir_t6 := tmp2
	if tir_t6 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t6, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t6].aux = hi
	tir_t7 := tmp2
	if tir_t7 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t7, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t7].opts = uint32(tir_b(greedy))
	tir_t8 := tmp2
	if tir_t8 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t8, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t8].first = tmp5
	tir_t9 := tmp2
	if tir_t9 >= uint32(len((*w).nodes)) {
		tir_oob(tir_t9, uint32(len((*w).nodes)))
	}
	(*w).nodes[tir_t9].last = tmp5
}

func at_line_end(subj []byte, pos uint32, nltype uint32) bool {
	var tmp1 uint32 = uint32(len(subj))
	if (pos >= tmp1) {
		return true
	}
	var tmp2 uint32 = uint32(0)
	tir_t1 := newline_at(subj, pos, nltype)
	tmp2 = tir_t1
	return ((tmp2 != uint32(0)) && (tmp1 == (pos + tmp2)))
}

func attach_atom(w *Work, kind Nd, val uint32, aux uint32) {
	var tmp1 uint32 = uint32(0)
	var tmp2 Nd = kind
	var tmp3 uint32 = val
	var tmp4 uint32 = aux
	tir_t1 := alloc_node(w, tmp2, tmp3, tmp4, uint32(0))
	tmp1 = tir_t1
	if ((*w).err != uint32(0)) {
		return
	}
	var tmp5 uint32 = (uint32(len((*w).frames)) - uint32(1))
	var tmp6 uint32 = (*w).frames[tmp5].cat
	add_child(w, tmp6, tmp1)
	tir_t2 := tmp5
	if tir_t2 >= uint32(len((*w).frames)) {
		tir_oob(tir_t2, uint32(len((*w).frames)))
	}
	(*w).frames[tir_t2].qual = tmp1
}

func attach_escape(w *Work, esc Esc) {
	switch esc.kind {
	case EkChar:
		var tmp1 uint32 = esc.val
		add_char(w, tmp1)
	case EkSet:
		class_from_set(w, esc.val, false)
	case EkNegSet:
		class_from_set(w, esc.val, true)
	case EkSod:
		attach_atom(w, NdSod, uint32(0), uint32(0))
	case EkEod:
		attach_atom(w, NdEod, uint32(0), uint32(0))
	case EkEodn:
		attach_atom(w, NdEodn, uint32(0), uint32(0))
	case EkWordB:
		attach_atom(w, NdWordB, uint32(0), uint32(0))
	case EkNotWordB:
		attach_atom(w, NdNotWordB, uint32(0), uint32(0))
	case EkBsr:
		attach_atom(w, NdBsr, uint32(0), uint32(0))
	case EkNop:
		attach_atom(w, NdNil, uint32(0), uint32(0))
	default:
	}
}

func bound_add(a Bound, b Bound) Bound {
	if ((!a.ok) || (!b.ok)) {
		return (Bound{ok: false, value: uint64(0)})
	}
	var over bool = false
	var total uint64
	tir_t1 := sat_add(a.value, b.value, &over)
	total = tir_t1
	if over {
		return (Bound{ok: false, value: uint64(0)})
	}
	return (Bound{ok: true, value: total})
}

func bound_mul(a Bound, b Bound) Bound {
	if ((!a.ok) || (!b.ok)) {
		return (Bound{ok: false, value: uint64(0)})
	}
	var over bool = false
	var total uint64
	tir_t1 := sat_mul(a.value, b.value, &over)
	total = tir_t1
	if over {
		return (Bound{ok: false, value: uint64(0)})
	}
	return (Bound{ok: true, value: total})
}

func bound_pow(base uint64, exp uint64) Bound {
	if (base == uint64(1)) {
		return (Bound{ok: true, value: uint64(1)})
	}
	if (base == uint64(0)) {
		if (exp == uint64(0)) {
			return (Bound{ok: true, value: uint64(1)})
		}
		return (Bound{ok: true, value: uint64(0)})
	}
	var out Bound = (Bound{ok: true, value: uint64(1)})
	var i uint64 = uint64(0)
	var one Bound
	for ((i < exp) && out.ok) {
		tir_t1 := bound_mul(out, (Bound{ok: true, value: base}))
		one = tir_t1
		out = one
		i = tir_cadd(i, uint64(1))
	}
	return out
}

func bsr_at(subj []byte, pos uint32, bsr uint32) uint32 {
	var tmp1 uint32 = uint32(len(subj))
	if (pos >= tmp1) {
		return uint32(0)
	}
	var tmp2 uint8 = subj[pos]
	if (tmp2 == uint8(13)) {
		if ((tmp1 > (pos + uint32(1))) && (subj[(pos + uint32(1))] == uint8(10))) {
			return uint32(2)
		}
		return uint32(1)
	}
	if (tmp2 == uint8(10)) {
		return uint32(1)
	}
	if (bsr == uint32(1)) {
		return uint32(0)
	}
	if ((tmp2 == uint8(11)) || ((tmp2 == uint8(12)) || (tmp2 == uint8(133)))) {
		return uint32(1)
	}
	return uint32(0)
}

func bt_match(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ov *[]uint32, use *Usage) uint32 {
	var regs []uint32
	_ = regs
	var bt []Bt
	_ = bt
	var trail []Undo
	_ = trail
	var tmp1 uint32 = uint32(1)
	tir_t1 := bt_run(re, subj, start, mopts, costlimit, stacklimit, memlimit, &regs, &bt, &trail, ov, use)
	tmp1 = tir_t1
	return tmp1
}

func bt_run(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, regs *[]uint32, bt *[]Bt, trail *[]Undo, ov *[]uint32, use *Usage) uint32 {
	var tmp1 uint32 = uint32(len(subj))
	var tmp2 uint64 = uint64(0)
	var tmp3 uint64 = uint64(0)
	_ = tmp3
	var tmp4 uint64 = uint64(0)
	var tmp5 uint32 = uint32(0)
	(*use).cost = tmp2
	(*use).stack = tmp5
	(*use).mem = tmp4
	if (start > tmp1) {
		return uint32(3)
	}
	var code []Inst = re.code
	var classes []byte = re.classes
	var reps []Rep = re.reps
	var tmp6 uint32 = re.nltype
	var tmp7 uint32 = re.bsr
	var tmp8 uint32 = re.ncap
	var tmp9 uint32 = re.nregs
	var tmp10 uint32 = ((tmp8 + uint32(1)) * uint32(2))
	var tmp11 uint32 = tmp10
	var tmp12 bool = (((re.opts & uint32(32)) != uint32(0)) || ((mopts & uint32(16)) != uint32(0)))
	var tmp13 bool = ((mopts & uint32(4)) != uint32(0))
	var tmp14 bool = ((mopts & uint32(8)) != uint32(0))
	var tmp15 bool = (re.hascrlf == uint32(0))
	var tmp16 bool = ((tmp6 == uint32(2)) || ((tmp6 == uint32(3)) || (tmp6 == uint32(4))))
	var tmp17 bool = ((mopts & uint32(1)) != uint32(0))
	var tmp18 bool = ((mopts & uint32(2)) != uint32(0))
	var tmp19 uint64 = tir_cmul(uint64((tmp9 + tmp10)), uint64(4))
	if ((tmp19 > memlimit) || (tmp19 > costlimit)) {
		return uint32(2)
	}
	tmp3 = tmp19
	tmp4 = tmp19
	tmp2 = tmp19
	tir_reserve(&(*regs), tmp9, 8704)
	tir_truncate(&(*regs), uint32(0))
	tir_truncate(&(*bt), uint32(0))
	tir_truncate(&(*trail), uint32(0))
	tir_reserve(&(*ov), tmp10, 512)
	var tmp20 uint32 = uint32(0)
	for (tmp20 < tmp9) {
		tir_push(&(*regs), 8704, uint32(4294967295))
		tmp20 = (tmp20 + uint32(1))
	}
	tir_truncate(&(*ov), uint32(0))
	tmp20 = uint32(0)
	for (tmp20 < tmp10) {
		tir_push(&(*ov), 512, uint32(4294967295))
		tmp20 = (tmp20 + uint32(1))
	}
	var tmp21 uint32 = start
	var tmp22 uint32 = uint32(1)
	var tmp23 bool = true
	var tmp24 bool = false
	tir_loop1:
	for tmp23 {
		var tmp25 uint64 = tir_cmul(uint64(tmp9), uint64(4))
		if (tmp25 > tir_csub(costlimit, tmp2)) {
			tmp22 = uint32(2)
			tmp23 = false
			continue tir_loop1
		}
		tmp2 = tir_cadd(tmp2, tmp25)
		var tmp26 uint32 = uint32(0)
		for (tmp26 < tmp9) {
			tir_t1 := tmp26
			if tir_t1 >= uint32(len((*regs))) {
				tir_oob(tir_t1, uint32(len((*regs))))
			}
			(*regs)[tir_t1] = uint32(4294967295)
			tmp26 = (tmp26 + uint32(1))
		}
		tir_truncate(&(*bt), uint32(0))
		tir_truncate(&(*trail), uint32(0))
		var tmp27 uint32 = uint32(0)
		var tmp28 uint32 = tmp21
		var tmp29 bool = true
		var tmp30 bool = false
		var tmp31 bool = false
		tir_loop2:
		for tmp29 {
			if (tmp2 >= costlimit) {
				tmp22 = uint32(2)
				tmp23 = false
				tmp29 = false
				continue tir_loop2
			}
			tmp2 = tir_cadd(tmp2, uint64(1))
			var tmp32 Inst = code[tmp27]
			switch tmp32.op {
			case OpChar:
				if ((tmp28 < tmp1) && (subj[tmp28] == uint8(tmp32.arg))) {
					tmp28 = (tmp28 + uint32(1))
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpCharCI:
				if ((tmp28 < tmp1) && (LOWER[uint32(subj[tmp28])] == uint8(tmp32.arg))) {
					tmp28 = (tmp28 + uint32(1))
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpClass:
				var tmp33 bool = false
				if (tmp28 < tmp1) {
					tir_t2 := class_has(classes, tmp32.arg, subj[tmp28])
					tmp33 = tir_t2
				}
				if ((tmp28 < tmp1) && tmp33) {
					tmp28 = (tmp28 + uint32(1))
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpAny:
				if ((tmp28 < tmp1) && true) {
					tmp28 = (tmp28 + uint32(1))
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpAnyNoNL:
				var tmp34 uint32 = uint32(0)
				if (tmp28 < tmp1) {
					tir_t3 := newline_at(subj, tmp28, tmp6)
					tmp34 = tir_t3
				}
				if ((tmp28 < tmp1) && (tmp34 == uint32(0))) {
					tmp28 = (tmp28 + uint32(1))
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpBsr:
				var tmp35 uint32 = uint32(0)
				tir_t4 := bsr_at(subj, tmp28, tmp7)
				tmp35 = tir_t4
				if (tmp35 != uint32(0)) {
					tmp28 = (tmp28 + tmp35)
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpSplit:
				var tmp36 uint32 = uint32(len((*trail)))
				tir_t5 := push_bt(bt, &tmp3, &tmp4, &tmp2, memlimit, costlimit, stacklimit, tmp32.alt, tmp28, tmp36)
				tmp24 = tir_t5
				if (!tmp24) {
					tmp22 = uint32(2)
					tmp23 = false
					tmp29 = false
				} else {
					if (tmp5 < uint32(len((*bt)))) {
						tmp5 = uint32(len((*bt)))
					}
				}
				tmp27 = tmp32.arg
			case OpJump:
				tmp27 = tmp32.arg
			case OpSave:
				tir_t6 := write_reg(regs, trail, &tmp3, &tmp4, &tmp2, memlimit, costlimit, uint32(len((*bt))), tmp32.arg, tmp28)
				tmp24 = tir_t6
				if (!tmp24) {
					tmp22 = uint32(2)
					tmp23 = false
					tmp29 = false
				}
				tmp27 = (tmp27 + uint32(1))
			case OpCirc:
				if ((tmp28 == uint32(0)) && (!tmp17)) {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpCircM:
				var tmp37 bool = (!tmp17)
				if (tmp28 != uint32(0)) {
					var tmp38 uint32 = uint32(0)
					tir_t7 := newline_before(subj, tmp28, tmp6)
					tmp38 = tir_t7
					tmp37 = ((tmp28 != tmp1) && (tmp38 != uint32(0)))
				}
				if tmp37 {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpDoll:
				var tmp39 bool = false
				tir_t8 := at_line_end(subj, tmp28, tmp6)
				tmp39 = tir_t8
				if ((!tmp18) && tmp39) {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpDollE:
				if ((!tmp18) && (tmp28 == tmp1)) {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpDollM:
				var tmp40 bool = (!tmp18)
				if (tmp28 < tmp1) {
					var tmp41 uint32 = uint32(0)
					tir_t9 := newline_at(subj, tmp28, tmp6)
					tmp41 = tir_t9
					tmp40 = (tmp41 != uint32(0))
				}
				if tmp40 {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpSod:
				if (tmp28 == uint32(0)) {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpEod:
				if (tmp28 == tmp1) {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpEodn:
				var tmp42 bool = false
				tir_t10 := at_line_end(subj, tmp28, tmp6)
				tmp42 = tir_t10
				if tmp42 {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpWordB:
				tir_t11 := word_edge(subj, tmp28)
				tmp24 = tir_t11
				if tmp24 {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpNotWordB:
				tir_t12 := word_edge(subj, tmp28)
				tmp24 = tir_t12
				if (!tmp24) {
					tmp27 = (tmp27 + uint32(1))
				} else {
					tmp30 = true
				}
			case OpRepZero:
				tir_t13 := write_reg(regs, trail, &tmp3, &tmp4, &tmp2, memlimit, costlimit, uint32(len((*bt))), (tmp11 + (tmp32.arg * uint32(2))), uint32(0))
				tmp24 = tir_t13
				if (!tmp24) {
					tmp22 = uint32(2)
					tmp23 = false
					tmp29 = false
				}
				tmp27 = (tmp27 + uint32(1))
			case OpRepEnter:
				tir_t14 := write_reg(regs, trail, &tmp3, &tmp4, &tmp2, memlimit, costlimit, uint32(len((*bt))), ((tmp11 + (tmp32.arg * uint32(2))) + uint32(1)), tmp28)
				tmp24 = tir_t14
				if (!tmp24) {
					tmp22 = uint32(2)
					tmp23 = false
					tmp29 = false
				}
				tmp27 = (tmp27 + uint32(1))
			case OpRepLoop:
				var tmp43 Rep = reps[tmp32.arg]
				var tmp44 uint32 = (*regs)[(tmp11 + (tmp32.arg * uint32(2)))]
				if (tmp44 < tmp43.lo) {
					tmp27 = tmp43.body
				} else {
					if (tmp44 >= tmp43.hi) {
						tmp27 = tmp43.after
					} else {
						if tmp43.greedy {
							var tmp45 uint32 = uint32(len((*trail)))
							tir_t15 := push_bt(bt, &tmp3, &tmp4, &tmp2, memlimit, costlimit, stacklimit, tmp43.after, tmp28, tmp45)
							tmp24 = tir_t15
							if (!tmp24) {
								tmp22 = uint32(2)
								tmp23 = false
								tmp29 = false
							} else {
								if (tmp5 < uint32(len((*bt)))) {
									tmp5 = uint32(len((*bt)))
								}
							}
							tmp27 = tmp43.body
						} else {
							var tmp46 uint32 = uint32(len((*trail)))
							tir_t16 := push_bt(bt, &tmp3, &tmp4, &tmp2, memlimit, costlimit, stacklimit, tmp43.body, tmp28, tmp46)
							tmp24 = tir_t16
							if (!tmp24) {
								tmp22 = uint32(2)
								tmp23 = false
								tmp29 = false
							} else {
								if (tmp5 < uint32(len((*bt)))) {
									tmp5 = uint32(len((*bt)))
								}
							}
							tmp27 = tmp43.after
						}
					}
				}
			case OpRepNext:
				var tmp47 Rep = reps[tmp32.arg]
				var tmp48 uint32 = (tmp11 + (tmp32.arg * uint32(2)))
				var tmp49 uint32 = ((*regs)[tmp48] + uint32(1))
				var tmp50 uint32 = (*regs)[(tmp48 + uint32(1))]
				tir_t17 := write_reg(regs, trail, &tmp3, &tmp4, &tmp2, memlimit, costlimit, uint32(len((*bt))), tmp48, tmp49)
				tmp24 = tir_t17
				if (!tmp24) {
					tmp22 = uint32(2)
					tmp23 = false
					tmp29 = false
				}
				if ((tmp47.hi == uint32(4294967295)) && ((tmp28 == tmp50) && (tmp49 >= tmp47.lo))) {
					tmp27 = tmp47.after
				} else {
					tmp27 = tmp47.head
				}
			case OpAccept:
				var tmp51 bool = (tmp28 == tmp21)
				var tmp52 bool = (tmp51 && (tmp13 || (tmp14 && (tmp21 == start))))
				if tmp52 {
					tmp30 = true
				} else {
					tir_t18 := uint32(0)
					if tir_t18 >= uint32(len((*regs))) {
						tir_oob(tir_t18, uint32(len((*regs))))
					}
					(*regs)[tir_t18] = tmp21
					tir_t19 := uint32(1)
					if tir_t19 >= uint32(len((*regs))) {
						tir_oob(tir_t19, uint32(len((*regs))))
					}
					(*regs)[tir_t19] = tmp28
					tmp31 = true
					tmp29 = false
				}
			}
			if tmp30 {
				if (uint32(len((*bt))) == uint32(0)) {
					tmp29 = false
					tir_truncate(&(*trail), uint32(0))
				} else {
					var tmp53 Bt
					tmp53 = tir_pop(&(*bt))
					tmp27 = tmp53.pc
					tmp28 = tmp53.pos
					var tmp54 uint64 = tir_cmul(tir_csub(uint64(uint32(len((*trail)))), uint64(tmp53.mark)), uint64(4))
					if (tmp54 > tir_csub(costlimit, tmp2)) {
						tmp22 = uint32(2)
						tmp23 = false
						tmp29 = false
					} else {
						tmp2 = tir_cadd(tmp2, tmp54)
						for (tmp53.mark < uint32(len((*trail)))) {
							var tmp55 Undo
							tmp55 = tir_pop(&(*trail))
							tir_t20 := tmp55.slot
							if tir_t20 >= uint32(len((*regs))) {
								tir_oob(tir_t20, uint32(len((*regs))))
							}
							(*regs)[tir_t20] = tmp55.old
						}
						if (uint32(len((*bt))) == uint32(0)) {
							tir_truncate(&(*trail), uint32(0))
						}
						tmp30 = false
					}
				}
			}
		}
		if tmp31 {
			tmp22 = uint32(0)
			tmp23 = false
			continue tir_loop1
		}
		if (!tmp23) {
			continue tir_loop1
		}
		if (tmp12 || (tmp21 >= tmp1)) {
			tmp23 = false
			continue tir_loop1
		}
		tmp21 = (tmp21 + uint32(1))
		if ((tmp16 && (tmp15 && (re.crfirst != uint32(0)))) && ((subj[(tmp21 - uint32(1))] == uint8(13)) && ((tmp21 < tmp1) && (subj[tmp21] == uint8(10))))) {
			tmp21 = (tmp21 + uint32(1))
		}
	}
	if (tmp22 == uint32(0)) {
		var tmp56 uint64 = tir_cmul(uint64(tmp10), uint64(4))
		if (tmp56 > tir_csub(costlimit, tmp2)) {
			tmp22 = uint32(2)
		} else {
			tmp2 = tir_cadd(tmp2, tmp56)
			var tmp57 uint32 = uint32(0)
			for (tmp57 < tmp10) {
				tir_t21 := tmp57
				if tir_t21 >= uint32(len((*ov))) {
					tir_oob(tir_t21, uint32(len((*ov))))
				}
				(*ov)[tir_t21] = (*regs)[tmp57]
				tmp57 = (tmp57 + uint32(1))
			}
		}
	}
	(*use).cost = tmp2
	(*use).stack = tmp5
	(*use).mem = tmp4
	return tmp22
}

func cert_bound(cert Cert, kind Bk, n uint64) Bound {
	var which Poly
	var ceiling uint64 = uint64(9007199254740991)
	var known bool = false
	switch kind {
	case BkCost:
		which = cert.cost
		known = true
	case BkStack:
		which = cert.stack
		ceiling = uint64(178956970)
		known = true
	case BkMem:
		which = cert.mem
		ceiling = uint64(2147483647)
		known = true
	}
	if (!known) {
		return (Bound{ok: false, value: uint64(0)})
	}
	var out Bound
	tir_t1 := poly_value(which, n)
	out = tir_t1
	if (out.ok && (out.value > ceiling)) {
		return (Bound{ok: false, value: uint64(0)})
	}
	return out
}

func cert_build(re Re, cert *Cert) Ar {
	var over bool = false
	var regions []Region = re.regions
	var total uint32 = uint32(len(regions))
	if (total == uint32(0)) {
		return ArShape
	}
	var prices []Price
	var kids []uint32
	var sibs []uint32
	_ = sibs
	var stop uint32 = uint32(len(re.code))
	var i uint32 = uint32(0)
	for (i < total) {
		var tmp1 Region = regions[i]
		if ((tmp1.lo > tmp1.hi) || (tmp1.hi > stop)) {
			return ArShape
		}
		if ((i > uint32(0)) && (tmp1.parent >= i)) {
			return ArShape
		}
		tir_push(&prices, 8208, (Price{work: (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), outs: (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), stack: (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), trail: (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})}))
		i = (i + uint32(1))
	}
	region_kids(regions, &kids, &sibs)
	i = total
	for (i > uint32(0)) {
		i = (i - uint32(1))
		var tmp2 Region = regions[i]
		var tmp3 Acc
		var tmp4 uint32 = kids[i]
		var tmp5 Ar = ArShape
		switch tmp2.kind {
		case RkRoot:
			tmp3.work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tir_t1 := price_span(re.code, regions, &prices, &sibs, tmp2.lo, tmp2.hi, tmp4, &tmp3, &over)
			tmp5 = tir_t1
		case RkGroup:
			tmp3.work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tir_t2 := price_span(re.code, regions, &prices, &sibs, tmp2.lo, tmp2.hi, tmp4, &tmp3, &over)
			tmp5 = tir_t2
		case RkBranch:
			tmp3.work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tir_t3 := price_span(re.code, regions, &prices, &sibs, tmp2.lo, tmp2.hi, tmp4, &tmp3, &over)
			tmp5 = tir_t3
		case RkAlt:
			tir_t4 := price_alt(&prices, &sibs, tmp4, &tmp3, &over)
			tmp5 = tir_t4
		case RkRepeat:
			tir_t5 := price_repeat(re.code, re.reps, regions, &prices, &sibs, i, tmp4, &tmp3, &over)
			tmp5 = tir_t5
		}
		if (tmp5 != ArOk) {
			return tmp5
		}
		if over {
			return ArOverflow
		}
		tir_t6 := i
		if tir_t6 >= uint32(len(prices)) {
			tir_oob(tir_t6, uint32(len(prices)))
		}
		prices[tir_t6] = (Price{work: tmp3.work, outs: tmp3.flow, stack: tmp3.stack, trail: tmp3.trail})
	}
	var root Price = prices[uint32(0)]
	price_call(re, root, cert, &over)
	if over {
		return ArOverflow
	}
	(*cert).config = CfgBacktrack
	(*cert).complexity = CcNotProvenLinear
	if (((((*cert).cost.base == uint64(1)) && ((*cert).cost.c2 == uint64(0))) && ((*cert).cost.c3 == uint64(0))) && ((*cert).cost.c4 == uint64(0))) {
		(*cert).complexity = CcLinear
	}
	(*cert).prices = prices
	prices = nil
	return ArOk
}

func cert_check(re Re, config Cfg, cert Cert) Cr {
	var over bool = false
	if (config == CfgPike) {
		var answered Cr = CrNoRules
		tir_t1 := pike_check(re, cert)
		answered = tir_t1
		return answered
	}
	if (config != CfgBacktrack) {
		return CrNoRules
	}
	if (cert.config != config) {
		return CrConfig
	}
	var shape Cr = CrOk
	tir_t2 := cert_shape(re)
	shape = tir_t2
	if (shape != CrOk) {
		return shape
	}
	var code []Inst = re.code
	var regions []Region = re.regions
	var prices []Price = cert.prices
	var total uint32 = uint32(len(regions))
	if (total != uint32(len(prices))) {
		return CrPrices
	}
	if (cert.cost.base == uint64(0)) {
		return CrBase
	}
	if (cert.stack.base == uint64(0)) {
		return CrBase
	}
	if (cert.trail.base == uint64(0)) {
		return CrBase
	}
	if (cert.mem.base == uint64(0)) {
		return CrBase
	}
	if ((cert.complexity != CcNotProvenLinear) && (cert.complexity != CcLinear)) {
		return CrShape
	}
	if (cert.complexity == CcLinear) {
		if (!((((cert.cost.base == uint64(1)) && (cert.cost.c2 == uint64(0))) && (cert.cost.c3 == uint64(0))) && (cert.cost.c4 == uint64(0)))) {
			return CrNotLinear
		}
	}
	var i uint32 = uint32(0)
	for (i < total) {
		var tmp1 Price = prices[i]
		if (tmp1.work.base == uint64(0)) {
			return CrBase
		}
		if (tmp1.outs.base == uint64(0)) {
			return CrBase
		}
		if (tmp1.stack.base == uint64(0)) {
			return CrBase
		}
		if (tmp1.trail.base == uint64(0)) {
			return CrBase
		}
		i = (i + uint32(1))
	}
	var kids []uint32
	var sibs []uint32
	_ = sibs
	region_kids(regions, &kids, &sibs)
	i = uint32(0)
	for (i < total) {
		var tmp2 Region = regions[i]
		var tmp3 Acc
		var tmp4 uint32 = kids[i]
		var tmp5 Cr = CrShape
		switch tmp2.kind {
		case RkRoot:
			tmp3.work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tir_t3 := scan_span(code, regions, prices, &sibs, tmp2.lo, tmp2.hi, tmp4, &tmp3, &over)
			tmp5 = tir_t3
		case RkGroup:
			tmp3.work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tir_t4 := scan_span(code, regions, prices, &sibs, tmp2.lo, tmp2.hi, tmp4, &tmp3, &over)
			tmp5 = tir_t4
		case RkBranch:
			tmp3.work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tmp3.flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
			tir_t5 := scan_span(code, regions, prices, &sibs, tmp2.lo, tmp2.hi, tmp4, &tmp3, &over)
			tmp5 = tir_t5
		case RkAlt:
			tir_t6 := scan_alt(prices, &sibs, tmp4, &tmp3, &over)
			tmp5 = tir_t6
		case RkRepeat:
			tir_t7 := scan_repeat(code, re.reps, regions, prices, &sibs, i, tmp4, &tmp3, &over)
			tmp5 = tir_t7
		}
		if (tmp5 != CrOk) {
			return tmp5
		}
		if over {
			return CrOverflow
		}
		var tmp6 bool = false
		var tmp7 Price = prices[i]
		tir_t8 := poly_ge(tmp7.work, tmp3.work)
		tmp6 = tir_t8
		if (!tmp6) {
			return CrRegionWork
		}
		tir_t9 := poly_ge(tmp7.outs, tmp3.flow)
		tmp6 = tir_t9
		if (!tmp6) {
			return CrRegionOuts
		}
		tir_t10 := poly_ge(tmp7.stack, tmp3.stack)
		tmp6 = tir_t10
		if (!tmp6) {
			return CrRegionStack
		}
		tir_t11 := poly_ge(tmp7.trail, tmp3.trail)
		tmp6 = tir_t11
		if (!tmp6) {
			return CrRegionTrail
		}
		i = (i + uint32(1))
	}
	var whole Price = prices[uint32(0)]
	var charged Cr = CrOk
	tir_t12 := charge_call(re, cert, whole, &over)
	charged = tir_t12
	if (charged != CrOk) {
		return charged
	}
	return CrOk
}

func cert_install(re Re, cert *Cert, has *bool, pcert *Cert, haspike *bool) Cr {
	(*has) = false
	(*haspike) = false
	var shape Cr = CrOk
	tir_t1 := cert_shape(re)
	shape = tir_t1
	if (shape != CrOk) {
		return shape
	}
	if re.pike {
		var tmp1 bool = false
		tir_t2 := pike_price(re, pcert)
		tmp1 = tir_t2
		if tmp1 {
			var tmp2 Cr = CrOk
			tir_t3 := cert_check(re, CfgPike, (*pcert))
			tmp2 = tir_t3
			if (tmp2 != CrOk) {
				return tmp2
			}
			(*haspike) = true
		}
	}
	var found Ar = ArShape
	tir_t4 := cert_build(re, cert)
	found = tir_t4
	if (found == ArShape) {
		return CrShape
	}
	if (found != ArOk) {
		return CrOk
	}
	var verdict Cr = CrOk
	tir_t5 := cert_check(re, CfgBacktrack, (*cert))
	verdict = tir_t5
	if (verdict != CrOk) {
		return verdict
	}
	(*has) = true
	return CrOk
}

func cert_shape(re Re) Cr {
	var code []Inst = re.code
	var regions []Region = re.regions
	var total uint32 = uint32(len(regions))
	if (total == uint32(0)) {
		return CrNoRegions
	}
	var root Region = regions[uint32(0)]
	if (root.kind != RkRoot) {
		return CrRootKind
	}
	if (root.parent != uint32(4294967295)) {
		return CrRootParent
	}
	if ((root.lo != uint32(0)) || (root.hi != uint32(len(code)))) {
		return CrRootRange
	}
	var ends []uint32
	var i uint32 = uint32(0)
	for (i < total) {
		tir_push(&ends, 8208, regions[i].lo)
		i = (i + uint32(1))
	}
	i = uint32(1)
	for (i < total) {
		var tmp1 Region = regions[i]
		var tmp2 uint32 = tmp1.parent
		if (tmp1.kind == RkRoot) {
			return CrTwoRoots
		}
		if (tmp2 >= i) {
			return CrParentOrder
		}
		if (tmp1.lo > tmp1.hi) {
			return CrBackwards
		}
		var tmp3 Region = regions[tmp2]
		if ((tmp1.lo < tmp3.lo) || (tmp1.hi > tmp3.hi)) {
			return CrNotNested
		}
		if (tmp1.lo < ends[tmp2]) {
			return CrOverlap
		}
		if ((tmp1.kind == RkBranch) && (tmp3.kind != RkAlt)) {
			return CrChildren
		}
		tir_t1 := tmp2
		if tir_t1 >= uint32(len(ends)) {
			tir_oob(tir_t1, uint32(len(ends)))
		}
		ends[tir_t1] = tmp1.hi
		i = (i + uint32(1))
	}
	var kids []uint32
	var sibs []uint32
	_ = sibs
	region_kids(regions, &kids, &sibs)
	i = uint32(0)
	for (i < total) {
		var tmp4 Region = regions[i]
		var tmp5 uint32 = kids[i]
		var tmp6 Cr = CrShape
		switch tmp4.kind {
		case RkRoot:
			tir_t2 := shape_span(code, regions, &sibs, tmp4.lo, tmp4.hi, tmp5)
			tmp6 = tir_t2
		case RkGroup:
			tir_t3 := shape_span(code, regions, &sibs, tmp4.lo, tmp4.hi, tmp5)
			tmp6 = tir_t3
		case RkBranch:
			tir_t4 := shape_span(code, regions, &sibs, tmp4.lo, tmp4.hi, tmp5)
			tmp6 = tir_t4
		case RkAlt:
			tir_t5 := shape_alt(code, regions, &sibs, i, tmp5)
			tmp6 = tir_t5
		case RkRepeat:
			tir_t6 := shape_repeat(code, re.reps, regions, &sibs, i, tmp5)
			tmp6 = tir_t6
		}
		if (tmp6 != CrOk) {
			return tmp6
		}
		i = (i + uint32(1))
	}
	return CrOk
}

func charge_call(re Re, cert Cert, whole Price, over *bool) Cr {
	var novec uint64 = tir_cmul(tir_cadd(uint64(re.ncap), uint64(1)), uint64(2))
	var setup uint64 = tir_cmul(tir_cadd(uint64(re.nregs), novec), uint64(4))
	var deliver uint64 = tir_cmul(novec, uint64(4))
	var reset uint64 = tir_cmul(uint64(re.nregs), uint64(4))
	var capacity Poly
	var scratch Poly = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	var tmp1 Poly = whole.stack
	capacity = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (!(((((tmp1.c0 == uint64(0)) && (tmp1.c1 == uint64(0))) && (tmp1.c2 == uint64(0))) && (tmp1.c3 == uint64(0))) && (tmp1.c4 == uint64(0)))) {
		var tmp2 Poly
		tir_t1 := poly_mul(tmp1, (Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp2 = tir_t1
		var tmp3 Poly
		tir_t2 := poly_add((Poly{base: uint64(1), c0: uint64(4), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp2, over)
		tmp3 = tir_t2
		capacity = tmp3
	}
	var tmp4 Poly
	tir_t3 := poly_mul(capacity, (Poly{base: uint64(1), c0: uint64(12), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp4 = tir_t3
	var tmp5 Poly
	tir_t4 := poly_add(scratch, tmp4, over)
	tmp5 = tir_t4
	scratch = tmp5
	var tmp6 Poly = whole.trail
	capacity = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (!(((((tmp6.c0 == uint64(0)) && (tmp6.c1 == uint64(0))) && (tmp6.c2 == uint64(0))) && (tmp6.c3 == uint64(0))) && (tmp6.c4 == uint64(0)))) {
		var tmp7 Poly
		tir_t5 := poly_mul(tmp6, (Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp7 = tir_t5
		var tmp8 Poly
		tir_t6 := poly_add((Poly{base: uint64(1), c0: uint64(4), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp7, over)
		tmp8 = tir_t6
		capacity = tmp8
	}
	var tmp9 Poly
	tir_t7 := poly_mul(capacity, (Poly{base: uint64(1), c0: uint64(8), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp9 = tir_t7
	var tmp10 Poly
	tir_t8 := poly_add(scratch, tmp9, over)
	tmp10 = tir_t8
	scratch = tmp10
	var tmp11 Poly
	tir_t9 := poly_mul(whole.trail, (Poly{base: uint64(1), c0: uint64(4), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp11 = tir_t9
	var tmp12 Poly
	tir_t10 := poly_add(whole.work, tmp11, over)
	tmp12 = tir_t10
	var tmp13 Poly
	tir_t11 := poly_add((Poly{base: uint64(1), c0: reset, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp12, over)
	tmp13 = tir_t11
	var tmp14 Poly
	tir_t12 := poly_mul(tmp13, (Poly{base: uint64(1), c0: uint64(0), c1: uint64(1), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp14 = tir_t12
	var tmp15 Poly
	tir_t13 := poly_mul(scratch, (Poly{base: uint64(1), c0: uint64(3), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp15 = tir_t13
	var tmp16 Poly
	tir_t14 := poly_add(tmp14, tmp15, over)
	tmp16 = tir_t14
	var tmp17 Poly
	tir_t15 := poly_add((Poly{base: uint64(1), c0: tir_cadd(setup, deliver), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp16, over)
	tmp17 = tir_t15
	var tmp18 Poly
	tir_t16 := poly_mul(scratch, (Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp18 = tir_t16
	var tmp19 Poly
	tir_t17 := poly_add((Poly{base: uint64(1), c0: tir_cadd(setup, deliver), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp18, over)
	tmp19 = tir_t17
	if (*over) {
		return CrOverflow
	}
	var holds bool = false
	tir_t18 := poly_ge(cert.cost, tmp17)
	holds = tir_t18
	if (!holds) {
		return CrTotalCost
	}
	tir_t19 := poly_eq(cert.stack, whole.stack)
	holds = tir_t19
	if (!holds) {
		return CrTotalStack
	}
	tir_t20 := poly_eq(cert.trail, whole.trail)
	holds = tir_t20
	if (!holds) {
		return CrTotalTrail
	}
	tir_t21 := poly_ge(cert.mem, tmp19)
	holds = tir_t21
	if (!holds) {
		return CrTotalMem
	}
	return CrOk
}

func charge_grow(oldcap uint32, lenv uint32, esize uint32, maxv uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	if (lenv < oldcap) {
		return true
	}
	if (lenv >= maxv) {
		return false
	}
	var tmp1 uint32 = uint32(4)
	var tmp2 uint32 = (oldcap * uint32(2))
	if (tmp2 > uint32(4)) {
		tmp1 = tmp2
	}
	if (tmp1 > maxv) {
		tmp1 = maxv
	}
	var tmp3 uint64 = tir_cmul(uint64(tmp1), uint64(esize))
	var tmp4 uint64 = tir_cmul(uint64(oldcap), uint64(esize))
	if (tmp3 > tir_csub(memlimit, (*mem))) {
		return false
	}
	var tmp5 uint64 = tir_cadd(tmp3, tmp4)
	if (tmp5 > tir_csub(costlimit, (*cost))) {
		return false
	}
	(*cost) = tir_cadd((*cost), tmp5)
	var tmp6 uint64 = tir_cadd((*mem), tmp3)
	if (tmp6 > (*peak)) {
		(*peak) = tmp6
	}
	(*mem) = tir_csub(tmp6, tmp4)
	return true
}

func check_possess(w *Work) {
	var tmp1 uint32 = uint32(len((*w).nodes))
	var tmp2 uint32 = uint32(0)
	var tmp3 uint32 = uint32(0)
	var tmp4 bool = false
	var tmp5 uint32 = uint32(1)
	for (tmp5 < tmp1) {
		var tmp6 Node = (*w).nodes[tmp5]
		tir_t1 := identity_of(tmp6.kind, tmp6.aux)
		tmp3 = tir_t1
		if (tmp3 == uint32(1)) {
			tmp2 = (tmp2 | uint32(2))
		}
		if (tmp3 == uint32(2)) {
			tmp2 = (tmp2 | uint32(4))
		}
		if (tmp3 == uint32(3)) {
			tmp2 = (tmp2 | uint32(8))
		}
		if (tmp3 == uint32(4)) {
			tmp2 = (tmp2 | uint32(16))
		}
		if (tmp3 == uint32(5)) {
			tmp2 = (tmp2 | uint32(32))
		}
		if (tmp3 == uint32(6)) {
			tmp2 = (tmp2 | uint32(64))
		}
		if (tmp3 == uint32(7)) {
			tmp2 = (tmp2 | uint32(128))
		}
		if (tmp3 == uint32(8)) {
			tmp2 = (tmp2 | uint32(256))
		}
		if (tmp3 == uint32(9)) {
			tmp2 = (tmp2 | uint32(512))
		}
		if (tmp3 == uint32(10)) {
			tmp2 = (tmp2 | uint32(1024))
		}
		if (tmp3 == uint32(11)) {
			tmp2 = (tmp2 | uint32(2048))
		}
		if (tmp3 == uint32(12)) {
			tmp2 = (tmp2 | uint32(4096))
		}
		if (tmp3 == uint32(13)) {
			tmp2 = (tmp2 | uint32(8192))
		}
		if (tmp6.kind == NdRepeat) {
			if ((*w).nodes[tmp6.first].kind == NdGroup) {
				tmp4 = true
			}
		}
		tmp5 = (tmp5 + uint32(1))
	}
	var tmp7 uint32 = uint32(0)
	tmp5 = (tmp1 - uint32(1))
	for (tmp5 > uint32(0)) {
		var tmp8 Node = (*w).nodes[tmp5]
		if ((tmp8.kind == NdRepeat) && (tmp8.aux > tmp8.val)) {
			var tmp9 Node = (*w).nodes[tmp8.first]
			tir_t2 := identity_of(tmp9.kind, tmp9.aux)
			tmp3 = tir_t2
			var tmp10 uint32 = uint32(0)
			if (tmp3 == uint32(3)) {
				tmp10 = uint32(10752)
			}
			if (tmp3 == uint32(7)) {
				tmp10 = uint32(512)
			}
			if (tmp3 == uint32(9)) {
				tmp10 = uint32(144)
			}
			if (tmp3 == uint32(11)) {
				tmp10 = uint32(8)
			}
			if (tmp3 == uint32(13)) {
				tmp10 = uint32(8)
			}
			var tmp11 uint32 = tmp7
			if tmp4 {
				tmp11 = tmp2
			}
			if ((tmp10 & tmp11) != uint32(0)) {
				(*w).err = uint32(1000)
				(*w).erroff = uint32(0)
				return
			}
		}
		tir_t3 := identity_of(tmp8.kind, tmp8.aux)
		tmp3 = tir_t3
		if (tmp3 == uint32(1)) {
			tmp7 = (tmp7 | uint32(2))
		}
		if (tmp3 == uint32(2)) {
			tmp7 = (tmp7 | uint32(4))
		}
		if (tmp3 == uint32(3)) {
			tmp7 = (tmp7 | uint32(8))
		}
		if (tmp3 == uint32(4)) {
			tmp7 = (tmp7 | uint32(16))
		}
		if (tmp3 == uint32(5)) {
			tmp7 = (tmp7 | uint32(32))
		}
		if (tmp3 == uint32(6)) {
			tmp7 = (tmp7 | uint32(64))
		}
		if (tmp3 == uint32(7)) {
			tmp7 = (tmp7 | uint32(128))
		}
		if (tmp3 == uint32(8)) {
			tmp7 = (tmp7 | uint32(256))
		}
		if (tmp3 == uint32(9)) {
			tmp7 = (tmp7 | uint32(512))
		}
		if (tmp3 == uint32(10)) {
			tmp7 = (tmp7 | uint32(1024))
		}
		if (tmp3 == uint32(11)) {
			tmp7 = (tmp7 | uint32(2048))
		}
		if (tmp3 == uint32(12)) {
			tmp7 = (tmp7 | uint32(4096))
		}
		if (tmp3 == uint32(13)) {
			tmp7 = (tmp7 | uint32(8192))
		}
		tmp5 = (tmp5 - uint32(1))
	}
}

func class_after_set(w *Work, at uint32, pat []byte) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = at
	if (((tmp2 < tmp1) && (pat[tmp2] == uint8(45))) && ((tmp1 > (tmp2 + uint32(1))) && (pat[(tmp2 + uint32(1))] != uint8(93)))) {
		(*w).err = uint32(150)
		(*w).erroff = (tmp2 + uint32(1))
	}
}

func class_element(w *Work, at *uint32, quoting *bool, pat []byte, base uint32, lo uint32, fold bool) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 uint32 = base
	var tmp4 uint32 = lo
	var tmp5 bool = fold
	class_skip(pat, &tmp2, quoting)
	if (((tmp2 < tmp1) && (pat[tmp2] == uint8(45))) && (!(*quoting))) {
		var tmp6 uint32 = (tmp2 + uint32(1))
		var tmp7 bool = false
		class_skip(pat, &tmp6, &tmp7)
		if ((tmp6 < tmp1) && (tmp7 || (pat[tmp6] != uint8(93)))) {
			var tmp8 uint32 = uint32(4294967295)
			if tmp7 {
				tmp8 = uint32(pat[tmp6])
				tmp6 = (tmp6 + uint32(1))
			} else {
				if (pat[tmp6] == uint8(92)) {
					var tmp9 Esc
					tir_t1 := read_escape(pat, &tmp6, w, true)
					tmp9 = tir_t1
					if ((*w).err != uint32(0)) {
						return
					}
					if (tmp9.kind != EkChar) {
						(*w).err = uint32(150)
						(*w).erroff = tmp6
						return
					}
					tmp8 = tmp9.val
				} else {
					if ((pat[tmp6] == uint8(91)) && (tmp1 > (tmp6 + uint32(1)))) {
						if (((pat[(tmp6 + uint32(1))] == uint8(58)) || (pat[(tmp6 + uint32(1))] == uint8(46))) || (pat[(tmp6 + uint32(1))] == uint8(61))) {
							var tmp10 uint32 = uint32(4294967295)
							tir_t2 := posix_end(pat, (tmp6 + uint32(1)))
							tmp10 = tir_t2
							if (tmp10 != uint32(4294967295)) {
								(*w).err = uint32(150)
								(*w).erroff = (tmp10 + uint32(2))
								return
							}
						}
					}
					tmp8 = uint32(pat[tmp6])
					tmp6 = (tmp6 + uint32(1))
				}
			}
			if (tmp8 < tmp4) {
				(*w).err = uint32(108)
				(*w).erroff = tmp6
				return
			}
			note_element(w, tmp4, tmp8, true)
			set_range(w, tmp3, tmp4, tmp8, tmp5)
			(*quoting) = tmp7
			(*at) = tmp6
			return
		}
	}
	note_element(w, tmp4, tmp4, false)
	set_range(w, tmp3, tmp4, tmp4, tmp5)
	(*at) = tmp2
}

func class_from_set(w *Work, which uint32, neg bool) {
	var tmp1 uint32 = uint32(0)
	tir_t1 := new_class(w)
	tmp1 = tir_t1
	if ((*w).err != uint32(0)) {
		return
	}
	var tmp2 uint32 = (tmp1 * uint32(32))
	var tmp3 uint32 = which
	var tmp4 bool = neg
	set_union(w, tmp2, tmp3, tmp4)
	var tmp5 uint32 = uint32(0)
	if ((tmp3 == uint32(0)) && (tmp4 == false)) {
		tmp5 = uint32(2)
	}
	if ((tmp3 == uint32(0)) && (tmp4 == true)) {
		tmp5 = uint32(1)
	}
	if ((tmp3 == uint32(2)) && (tmp4 == false)) {
		tmp5 = uint32(4)
	}
	if ((tmp3 == uint32(2)) && (tmp4 == true)) {
		tmp5 = uint32(3)
	}
	if ((tmp3 == uint32(1)) && (tmp4 == false)) {
		tmp5 = uint32(6)
	}
	if ((tmp3 == uint32(1)) && (tmp4 == true)) {
		tmp5 = uint32(5)
	}
	if ((tmp3 == uint32(3)) && (tmp4 == false)) {
		tmp5 = uint32(11)
	}
	if ((tmp3 == uint32(3)) && (tmp4 == true)) {
		tmp5 = uint32(10)
	}
	if ((tmp3 == uint32(4)) && (tmp4 == false)) {
		tmp5 = uint32(13)
	}
	if ((tmp3 == uint32(4)) && (tmp4 == true)) {
		tmp5 = uint32(12)
	}
	attach_atom(w, NdClass, tmp1, tmp5)
}

func class_has(classes []byte, idx uint32, c uint8) bool {
	var tmp1 uint32 = ((idx * uint32(32)) + uint32((c >> 3)))
	var tmp2 uint8 = BITS[(uint32(c) & uint32(7))]
	return ((classes[tmp1] & tmp2) != uint8(0))
}

func class_skip(pat []byte, at *uint32, quoting *bool) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	tir_loop1:
	for (tmp1 > (tmp2 + uint32(1))) {
		if (pat[tmp2] != uint8(92)) {
			break tir_loop1
		}
		var tmp3 uint8 = pat[(tmp2 + uint32(1))]
		if (tmp3 == uint8(81)) {
			(*quoting) = true
			tmp2 = (tmp2 + uint32(2))
			continue tir_loop1
		}
		if (tmp3 == uint8(69)) {
			(*quoting) = false
			tmp2 = (tmp2 + uint32(2))
			continue tir_loop1
		}
		break tir_loop1
	}
	(*at) = tmp2
}

func close_group(w *Work) {
	var tmp1 Frame
	tmp1 = tir_pop(&(*w).frames)
	(*w).opts = tmp1.opts
	if (tmp1.unsup != uint32(0)) {
		(*w).err = uint32(1000)
		(*w).erroff = tmp1.unsup
		return
	}
	var tmp2 uint32 = (uint32(len((*w).frames)) - uint32(1))
	tir_t1 := tmp2
	if tir_t1 >= uint32(len((*w).frames)) {
		tir_oob(tir_t1, uint32(len((*w).frames)))
	}
	(*w).frames[tir_t1].qual = tmp1.grp
}

func close_region(w *Work, at uint32) {
	var tmp1 uint32 = at
	if (tmp1 >= uint32(len((*w).regions))) {
		return
	}
	tir_t1 := tmp1
	if tir_t1 >= uint32(len((*w).regions)) {
		tir_oob(tir_t1, uint32(len((*w).regions)))
	}
	(*w).regions[tir_t1].hi = uint32(len((*w).code))
}

func compile(pat []byte, popts uint32, nltype uint32, bsr uint32, out *Out) {
	(*out).err = uint32(0)
	(*out).erroff = uint32(0)
	var tmp1 uint32 = uint32(len(pat))
	if (tmp1 > uint32(4096)) {
		(*out).err = uint32(1002)
		return
	}
	var w Work
	parse(pat, popts, nltype, &w)
	if (w.err != uint32(0)) {
		(*out).err = w.err
		(*out).erroff = w.erroff
		return
	}
	var tmp2 bool = ((popts & uint32(64)) != uint32(0))
	generate(&w, tmp2)
	if (w.err != uint32(0)) {
		(*out).err = w.err
		(*out).erroff = w.erroff
		return
	}
	var tmp3 uint32 = (((w.ncap + uint32(1)) * uint32(2)) + (w.nrep * uint32(2)))
	if (tmp3 > uint32(8704)) {
		(*out).err = uint32(1002)
		return
	}
	(*out).re.ncap = w.ncap
	(*out).re.nname = w.nname
	(*out).re.nregs = tmp3
	(*out).re.opts = popts
	(*out).re.nltype = nltype
	(*out).re.bsr = bsr
	(*out).re.hascrlf = w.hascrlf
	(*out).re.crfirst = w.crfirst
	(*out).re.code = w.code
	w.code = nil
	(*out).re.classes = w.classes
	w.classes = nil
	(*out).re.reps = w.reps
	w.reps = nil
	(*out).re.regions = w.regions
	w.regions = nil
	(*out).re.names = w.names
	w.names = nil
	(*out).re.nameents = w.nameents
	w.nameents = nil
	var tmp4 bool = false
	tir_t1 := pike_ok((*out).re)
	tmp4 = tir_t1
	(*out).re.pike = tmp4
	var cand Cert
	var tmp5 bool = false
	var pcand Cert
	var tmp6 bool = false
	var tmp7 Cr = CrOk
	tir_t2 := cert_install((*out).re, &cand, &tmp5, &pcand, &tmp6)
	tmp7 = tir_t2
	if (tmp7 != CrOk) {
		(*out).err = uint32(1003)
		return
	}
	(*out).re.cert = cand
	(*out).re.hascert = tmp5
	(*out).re.pikecert = pcand
	(*out).re.haspikecert = tmp6
}

func ct(c uint8, bit uint8) bool {
	return ((CTYPE[uint32(c)] & bit) != uint8(0))
}

func ctx_create(re Re, mcfg uint32, maxlen uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ctx *Ctx) uint32 {
	(*ctx).ready = false
	var answered Answer
	tir_t1 := re_mem(re, mcfg, uint64(maxlen))
	answered = tir_t1
	if (answered.status != uint32(0)) {
		return answered.status
	}
	var resident uint64 = answered.value
	var picked Cert
	var has bool = false
	tir_t2 := re_pick(re, &picked)
	has = tir_t2
	if (!has) {
		return uint32(4)
	}
	var over bool = false
	var novec uint32 = ((re.ncap + uint32(1)) * uint32(2))
	var answer uint64 = tir_cmul(uint64(novec), uint64(4))
	var setup uint64 = uint64(0)
	var ballast uint64 = uint64(0)
	var nregs uint32 = uint32(0)
	var cbt uint64 = uint64(0)
	var ctrail uint64 = uint64(0)
	var clists uint64 = uint64(0)
	var cstk uint64 = uint64(0)
	var ctab uint64 = uint64(0)
	var cpool uint64 = uint64(0)
	var words uint32 = uint32(0)
	if re.pike {
		var room Room
		pike_room(re, &room, &over)
		words = room.words
		clists = room.lists
		cstk = room.stk
		ctab = room.tables
		cpool = room.pool
		ballast = room.reserved
		setup = tir_cadd(tir_cmul(uint64(novec), uint64(4)), uint64(words))
	} else {
		var tmp1 Bound
		tir_t3 := poly_value(picked.stack, uint64(maxlen))
		tmp1 = tir_t3
		var tmp2 Bound
		tir_t4 := poly_value(picked.trail, uint64(maxlen))
		tmp2 = tir_t4
		if (!tmp1.ok) {
			return uint32(4)
		}
		if (!tmp2.ok) {
			return uint32(4)
		}
		var tmp3 uint64 = uint64(0)
		if (tmp1.value > uint64(0)) {
			var tmp4 uint64
			tir_t5 := sat_mul(tmp1.value, uint64(2), &over)
			tmp4 = tir_t5
			var tmp5 uint64
			tir_t6 := sat_add(tmp4, uint64(4), &over)
			tmp5 = tir_t6
			tmp3 = tmp5
		}
		cbt = tmp3
		var tmp6 uint64 = uint64(0)
		if (tmp2.value > uint64(0)) {
			var tmp7 uint64
			tir_t7 := sat_mul(tmp2.value, uint64(2), &over)
			tmp7 = tir_t7
			var tmp8 uint64
			tir_t8 := sat_add(tmp7, uint64(4), &over)
			tmp8 = tir_t8
			tmp6 = tmp8
		}
		ctrail = tmp6
		var tmp9 uint64
		tir_t9 := sat_mul(cbt, uint64(12), &over)
		tmp9 = tir_t9
		var tmp10 uint64
		tir_t10 := sat_mul(ctrail, uint64(8), &over)
		tmp10 = tir_t10
		var tmp11 uint64
		tir_t11 := sat_add(tmp9, tmp10, &over)
		tmp11 = tir_t11
		tmp9 = tmp11
		ballast = tmp9
		nregs = re.nregs
		setup = tir_cmul(uint64((nregs + novec)), uint64(4))
	}
	var tmp12 uint64
	tir_t12 := sat_add(setup, answer, &over)
	tmp12 = tir_t12
	var tmp13 uint64
	tir_t13 := sat_add(tmp12, ballast, &over)
	tmp13 = tir_t13
	var tmp14 uint64 = tmp13
	if over {
		return uint32(4)
	}
	if (tmp14 > resident) {
		return uint32(4)
	}
	if (resident > memlimit) {
		return uint32(2)
	}
	if (resident > costlimit) {
		return uint32(2)
	}
	var blank Ctx
	_ = blank
	tir_t14 := (*ctx)
	(*ctx) = blank
	blank = tir_t14
	tir_reserve(&(*ctx).regs, nregs, 8704)
	tir_reserve(&(*ctx).bt, uint32(cbt), 178956970)
	tir_reserve(&(*ctx).trail, uint32(ctrail), 268435455)
	tir_reserve(&(*ctx).clist, uint32(clists), 65700)
	tir_reserve(&(*ctx).nlist, uint32(clists), 65700)
	tir_reserve(&(*ctx).stk, uint32(cstk), 131396)
	tir_reserve(&(*ctx).seen, words, 2147483647)
	tir_reserve(&(*ctx).rc, uint32(ctab), 262796)
	tir_reserve(&(*ctx).free, uint32(ctab), 262796)
	tir_reserve(&(*ctx).pool, uint32(cpool), 134549508)
	tir_reserve(&(*ctx).slack, uint32(tir_csub(resident, tmp14)), 2147483647)
	(*ctx).re = re
	(*ctx).maxlen = maxlen
	(*ctx).costcap = costlimit
	(*ctx).stackcap = stacklimit
	(*ctx).memcap = resident
	(*ctx).ready = true
	return uint32(0)
}

func ctx_match(ctx *Ctx, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, ov *[]uint32, use *Usage) uint32 {
	(*use).cost = uint64(0)
	(*use).stack = uint32(0)
	(*use).mem = uint64(0)
	if (!(*ctx).ready) {
		return uint32(3)
	}
	if ((*ctx).maxlen < uint32(len(subj))) {
		return uint32(3)
	}
	if (costlimit > (*ctx).costcap) {
		return uint32(3)
	}
	if (stacklimit > (*ctx).stackcap) {
		return uint32(3)
	}
	var tmp1 uint32 = uint32(1)
	if (*ctx).re.pike {
		tir_t1 := pike_run((*ctx).re, subj, start, mopts, costlimit, stacklimit, (*ctx).memcap, &(*ctx).clist, &(*ctx).nlist, &(*ctx).stk, &(*ctx).seen, &(*ctx).pool, &(*ctx).rc, &(*ctx).free, ov, use)
		tmp1 = tir_t1
	} else {
		tir_t2 := bt_run((*ctx).re, subj, start, mopts, costlimit, stacklimit, (*ctx).memcap, &(*ctx).regs, &(*ctx).bt, &(*ctx).trail, ov, use)
		tmp1 = tir_t2
	}
	(*use).mem = (*ctx).memcap
	return tmp1
}

func drop_empty_region(w *Work, at uint32) {
	var tmp1 uint32 = at
	if (tmp1 >= uint32(len((*w).regions))) {
		return
	}
	if ((*w).regions[tmp1].lo == uint32(len((*w).code))) {
		tir_truncate(&(*w).regions, tmp1)
	}
}

func emit(w *Work, op Op, arg uint32, alt uint32) uint32 {
	var tmp1 uint32 = uint32(len((*w).code))
	if (tmp1 >= uint32(32848)) {
		(*w).err = uint32(1002)
		return uint32(0)
	}
	tir_push(&(*w).code, 32848, (Inst{op: op, arg: arg, alt: alt}))
	return tmp1
}

func generate(w *Work, endanchored bool) {
	var tmp1 uint32 = (*w).root
	var tmp2 uint32 = uint32(0)
	tir_t1 := open_region(w, RkRoot, uint32(4294967295))
	tmp2 = tir_t1
	push_job(w, tmp1, tmp2)
	var tmp3 uint64 = uint64(65664)
	var tmp4 uint32 = uint32(0)
	_ = tmp4
	for (((uint32(len((*w).jobs)) > uint32(0)) && (tmp3 > uint64(0))) && ((*w).err == uint32(0))) {
		tmp3 = tir_csub(tmp3, uint64(1))
		var tmp5 uint32 = (uint32(len((*w).jobs)) - uint32(1))
		var tmp6 Job = (*w).jobs[tmp5]
		var tmp7 Node = (*w).nodes[tmp6.node]
		var tmp8 Job
		_ = tmp8
		switch tmp7.kind {
		case NdNil:
			tmp8 = tir_pop(&(*w).jobs)
		case NdChar:
			tir_t2 := emit(w, OpChar, tmp7.val, uint32(0))
			tmp4 = tir_t2
			tmp8 = tir_pop(&(*w).jobs)
		case NdCharCI:
			tir_t3 := emit(w, OpCharCI, tmp7.val, uint32(0))
			tmp4 = tir_t3
			tmp8 = tir_pop(&(*w).jobs)
		case NdClass:
			tir_t4 := emit(w, OpClass, tmp7.val, uint32(0))
			tmp4 = tir_t4
			tmp8 = tir_pop(&(*w).jobs)
		case NdAny:
			tir_t5 := emit(w, OpAny, tmp7.val, uint32(0))
			tmp4 = tir_t5
			tmp8 = tir_pop(&(*w).jobs)
		case NdAnyNoNL:
			tir_t6 := emit(w, OpAnyNoNL, tmp7.val, uint32(0))
			tmp4 = tir_t6
			tmp8 = tir_pop(&(*w).jobs)
		case NdBsr:
			tir_t7 := emit(w, OpBsr, tmp7.val, uint32(0))
			tmp4 = tir_t7
			tmp8 = tir_pop(&(*w).jobs)
		case NdCirc:
			tir_t8 := emit(w, OpCirc, tmp7.val, uint32(0))
			tmp4 = tir_t8
			tmp8 = tir_pop(&(*w).jobs)
		case NdCircM:
			tir_t9 := emit(w, OpCircM, tmp7.val, uint32(0))
			tmp4 = tir_t9
			tmp8 = tir_pop(&(*w).jobs)
		case NdDoll:
			tir_t10 := emit(w, OpDoll, tmp7.val, uint32(0))
			tmp4 = tir_t10
			tmp8 = tir_pop(&(*w).jobs)
		case NdDollE:
			tir_t11 := emit(w, OpDollE, tmp7.val, uint32(0))
			tmp4 = tir_t11
			tmp8 = tir_pop(&(*w).jobs)
		case NdDollM:
			tir_t12 := emit(w, OpDollM, tmp7.val, uint32(0))
			tmp4 = tir_t12
			tmp8 = tir_pop(&(*w).jobs)
		case NdSod:
			tir_t13 := emit(w, OpSod, tmp7.val, uint32(0))
			tmp4 = tir_t13
			tmp8 = tir_pop(&(*w).jobs)
		case NdEod:
			tir_t14 := emit(w, OpEod, tmp7.val, uint32(0))
			tmp4 = tir_t14
			tmp8 = tir_pop(&(*w).jobs)
		case NdEodn:
			tir_t15 := emit(w, OpEodn, tmp7.val, uint32(0))
			tmp4 = tir_t15
			tmp8 = tir_pop(&(*w).jobs)
		case NdWordB:
			tir_t16 := emit(w, OpWordB, tmp7.val, uint32(0))
			tmp4 = tir_t16
			tmp8 = tir_pop(&(*w).jobs)
		case NdNotWordB:
			tir_t17 := emit(w, OpNotWordB, tmp7.val, uint32(0))
			tmp4 = tir_t17
			tmp8 = tir_pop(&(*w).jobs)
		case NdConcat:
			var tmp9 uint32 = tmp7.first
			if (tmp6.phase != uint32(0)) {
				tmp9 = (*w).nodes[tmp6.cur].nxt
			}
			if (tmp9 == uint32(0)) {
				tmp8 = tir_pop(&(*w).jobs)
			} else {
				tir_t18 := tmp5
				if tir_t18 >= uint32(len((*w).jobs)) {
					tir_oob(tir_t18, uint32(len((*w).jobs)))
				}
				(*w).jobs[tir_t18].phase = uint32(1)
				tir_t19 := tmp5
				if tir_t19 >= uint32(len((*w).jobs)) {
					tir_oob(tir_t19, uint32(len((*w).jobs)))
				}
				(*w).jobs[tir_t19].cur = tmp9
				push_job(w, tmp9, tmp6.here)
			}
		case NdGroup:
			if (tmp6.phase == uint32(0)) {
				var tmp10 uint32 = uint32(0)
				tir_t20 := open_region(w, RkGroup, tmp6.here)
				tmp10 = tir_t20
				tir_t21 := tmp5
				if tir_t21 >= uint32(len((*w).jobs)) {
					tir_oob(tir_t21, uint32(len((*w).jobs)))
				}
				(*w).jobs[tir_t21].here = tmp10
				if (tmp7.val != uint32(0)) {
					var tmp11 uint32 = (tmp7.val * uint32(2))
					tir_t22 := emit(w, OpSave, tmp11, uint32(0))
					tmp4 = tir_t22
				}
				tir_t23 := tmp5
				if tir_t23 >= uint32(len((*w).jobs)) {
					tir_oob(tir_t23, uint32(len((*w).jobs)))
				}
				(*w).jobs[tir_t23].phase = uint32(1)
				var tmp12 uint32 = tmp7.first
				if (tmp12 != uint32(0)) {
					push_job(w, tmp12, tmp10)
				}
			} else {
				if (tmp7.val != uint32(0)) {
					var tmp13 uint32 = ((tmp7.val * uint32(2)) + uint32(1))
					tir_t24 := emit(w, OpSave, tmp13, uint32(0))
					tmp4 = tir_t24
				}
				close_region(w, tmp6.here)
				drop_empty_region(w, tmp6.here)
				tmp8 = tir_pop(&(*w).jobs)
			}
		case NdAlt:
			walk_alt(w, tmp5, tmp6, tmp7)
		case NdRepeat:
			walk_repeat(w, tmp5, tmp6, tmp7)
		}
	}
	if ((*w).err != uint32(0)) {
		return
	}
	if (tmp3 == uint64(0)) {
		(*w).err = uint32(1003)
		return
	}
	if endanchored {
		tir_t25 := emit(w, OpEod, uint32(0), uint32(0))
		tmp4 = tir_t25
	}
	tir_t26 := emit(w, OpAccept, uint32(0), uint32(0))
	tmp4 = tir_t26
	close_region(w, tmp2)
	if ((*w).err == uint32(0)) {
		scan_first(w)
	}
}

func hex_value(c uint8) uint32 {
	if (c <= uint8(57)) {
		return uint32((c - uint8(48)))
	}
	return uint32((((c | uint8(32)) - uint8(97)) + uint8(10)))
}

func identity_of(kind Nd, aux uint32) uint32 {
	switch kind {
	case NdClass:
		return aux
	case NdAnyNoNL:
		return uint32(7)
	case NdAny:
		return uint32(8)
	case NdBsr:
		return uint32(9)
	default:
		return uint32(0)
	}
}

func mark_seen(w *Work, pc uint32) {
	var tmp1 uint32 = pc
	if (tmp1 >= uint32(len((*w).code))) {
		return
	}
	var tmp2 uint32 = (tmp1 >> 3)
	var tmp3 uint8 = BITS[(tmp1 & uint32(7))]
	if (((*w).seen[tmp2] & tmp3) != uint8(0)) {
		return
	}
	tir_t1 := tmp2
	if tir_t1 >= uint32(len((*w).seen)) {
		tir_oob(tir_t1, uint32(len((*w).seen)))
	}
	(*w).seen[tir_t1] = ((*w).seen[tmp2] | tmp3)
	tir_push(&(*w).pending, 32848, tmp1)
}

func match(re Re, subj []byte, start uint32, mopts uint32, mcfg uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ov *[]uint32, use *Usage) uint32 {
	(*use).cost = uint64(0)
	(*use).stack = uint32(0)
	(*use).mem = uint64(0)
	if (mcfg != uint32(0)) {
		return uint32(3)
	}
	var tmp1 uint32 = uint32(1)
	if re.pike {
		tir_t1 := pike_match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use)
		tmp1 = tir_t1
		return tmp1
	}
	tir_t2 := bt_match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use)
	tmp1 = tir_t2
	return tmp1
}

func name_taken(pat []byte, off uint32, nlen uint32, w *Work) bool {
	var tmp1 uint32 = uint32(0)
	var tmp2 uint32 = uint32(len((*w).nameents))
	for (tmp1 < tmp2) {
		var tmp3 NameEnt = (*w).nameents[tmp1]
		if (tmp3.nlen == nlen) {
			var tmp4 uint32 = uint32(0)
			var tmp5 bool = true
			tir_loop1:
			for (tmp4 < nlen) {
				if ((*w).names[(tmp3.off + tmp4)] != pat[(off + tmp4)]) {
					tmp5 = false
					break tir_loop1
				}
				tmp4 = (tmp4 + uint32(1))
			}
			if tmp5 {
				return true
			}
		}
		tmp1 = (tmp1 + uint32(1))
	}
	return false
}

func named_group(pat []byte, at *uint32, w *Work, start uint32, term uint8, here uint32) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = start
	var tmp3 bool = false
	if (tmp2 < tmp1) {
		tir_t1 := ct(pat[tmp2], uint8(4))
		tmp3 = tir_t1
	}
	if tmp3 {
		(*w).err = uint32(144)
		(*w).erroff = (tmp2 + uint32(1))
		return
	}
	var tmp4 uint32 = tmp2
	var tmp5 bool = false
	tir_loop1:
	for (tmp4 < tmp1) {
		tir_t2 := ct(pat[tmp4], uint8(1))
		tmp5 = tir_t2
		if (!tmp5) {
			break tir_loop1
		}
		tmp4 = (tmp4 + uint32(1))
	}
	var tmp6 uint32 = (tmp4 - tmp2)
	if (tmp6 == uint32(0)) {
		(*w).err = uint32(162)
		(*w).erroff = tmp2
		return
	}
	if (tmp6 > uint32(128)) {
		(*w).err = uint32(148)
		(*w).erroff = tmp4
		return
	}
	if ((tmp4 >= tmp1) || (pat[tmp4] != term)) {
		(*w).err = uint32(142)
		(*w).erroff = tmp4
		return
	}
	var tmp7 bool = false
	tir_t3 := name_taken(pat, tmp2, tmp6, w)
	tmp7 = tir_t3
	if tmp7 {
		(*w).err = uint32(143)
		(*w).erroff = (tmp4 + uint32(1))
		return
	}
	if (((*w).ncap >= uint32(255)) || (((*w).nname >= uint32(255)) || ((uint32(len((*w).names)) + tmp6) > uint32(4096)))) {
		(*w).err = uint32(1002)
		return
	}
	var tmp8 uint32 = ((*w).ncap + uint32(1))
	(*w).ncap = tmp8
	var tmp9 uint32 = uint32(len((*w).names))
	tir_push(&(*w).nameents, 255, (NameEnt{off: tmp9, nlen: tmp6, grp: tmp8}))
	(*w).nname = ((*w).nname + uint32(1))
	var tmp10 uint32 = uint32(0)
	for (tmp10 < tmp6) {
		var tmp11 uint8 = pat[(tmp2 + tmp10)]
		tir_push(&(*w).names, 2147483647, tmp11)
		tmp10 = (tmp10 + uint32(1))
	}
	var tmp12 uint32 = (*w).opts
	var tmp13 uint32 = here
	push_frame(w, tmp8, tmp12, tmp13, uint32(0))
	(*at) = (tmp4 + uint32(1))
}

func new_branch(w *Work) {
	var tmp1 uint32 = (uint32(len((*w).frames)) - uint32(1))
	var tmp2 uint32 = (*w).frames[tmp1].alt
	if (tmp2 == uint32(0)) {
		var tmp3 uint32 = uint32(0)
		tir_t1 := alloc_node(w, NdAlt, uint32(0), uint32(0), uint32(0))
		tmp3 = tir_t1
		if ((*w).err != uint32(0)) {
			return
		}
		var tmp4 uint32 = (*w).frames[tmp1].grp
		var tmp5 uint32 = (*w).nodes[tmp4].first
		tir_t2 := tmp3
		if tir_t2 >= uint32(len((*w).nodes)) {
			tir_oob(tir_t2, uint32(len((*w).nodes)))
		}
		(*w).nodes[tir_t2].first = tmp5
		tir_t3 := tmp3
		if tir_t3 >= uint32(len((*w).nodes)) {
			tir_oob(tir_t3, uint32(len((*w).nodes)))
		}
		(*w).nodes[tir_t3].last = tmp5
		tir_t4 := tmp4
		if tir_t4 >= uint32(len((*w).nodes)) {
			tir_oob(tir_t4, uint32(len((*w).nodes)))
		}
		(*w).nodes[tir_t4].first = tmp3
		tir_t5 := tmp4
		if tir_t5 >= uint32(len((*w).nodes)) {
			tir_oob(tir_t5, uint32(len((*w).nodes)))
		}
		(*w).nodes[tir_t5].last = tmp3
		tir_t6 := tmp1
		if tir_t6 >= uint32(len((*w).frames)) {
			tir_oob(tir_t6, uint32(len((*w).frames)))
		}
		(*w).frames[tir_t6].alt = tmp3
		tmp2 = tmp3
	}
	var tmp6 uint32 = uint32(0)
	tir_t7 := alloc_node(w, NdConcat, uint32(0), uint32(0), uint32(0))
	tmp6 = tir_t7
	if ((*w).err != uint32(0)) {
		return
	}
	add_child(w, tmp2, tmp6)
	tir_t8 := tmp1
	if tir_t8 >= uint32(len((*w).frames)) {
		tir_oob(tir_t8, uint32(len((*w).frames)))
	}
	(*w).frames[tir_t8].cat = tmp6
	tir_t9 := tmp1
	if tir_t9 >= uint32(len((*w).frames)) {
		tir_oob(tir_t9, uint32(len((*w).frames)))
	}
	(*w).frames[tir_t9].qual = uint32(0)
}

func new_class(w *Work) uint32 {
	if ((*w).nclass >= uint32(4096)) {
		(*w).err = uint32(1002)
		return uint32(0)
	}
	var tmp1 uint32 = uint32(0)
	for (tmp1 < uint32(32)) {
		tir_push(&(*w).classes, 2147483647, uint8(0))
		tmp1 = (tmp1 + uint32(1))
	}
	var tmp2 uint32 = (*w).nclass
	(*w).nclass = (tmp2 + uint32(1))
	return tmp2
}

func new_rep(w *Work) uint32 {
	var tmp1 uint32 = (*w).nrep
	if (tmp1 >= uint32(4096)) {
		(*w).err = uint32(1002)
		return uint32(0)
	}
	tir_push(&(*w).reps, 4096, (Rep{lo: uint32(0), hi: uint32(0), greedy: true, head: uint32(0), body: uint32(0), after: uint32(0)}))
	(*w).nrep = (tmp1 + uint32(1))
	return tmp1
}

func newline_at(subj []byte, pos uint32, nltype uint32) uint32 {
	var tmp1 uint32 = uint32(len(subj))
	if (pos >= tmp1) {
		return uint32(0)
	}
	var tmp2 uint8 = subj[pos]
	if (nltype == uint32(0)) {
		if (tmp2 == uint8(10)) {
			return uint32(1)
		}
		return uint32(0)
	}
	if (nltype == uint32(1)) {
		if (tmp2 == uint8(13)) {
			return uint32(1)
		}
		return uint32(0)
	}
	if (nltype == uint32(2)) {
		if ((tmp2 == uint8(13)) && ((tmp1 > (pos + uint32(1))) && (subj[(pos + uint32(1))] == uint8(10)))) {
			return uint32(2)
		}
		return uint32(0)
	}
	if (tmp2 == uint8(10)) {
		return uint32(1)
	}
	if (tmp2 == uint8(13)) {
		if ((tmp1 > (pos + uint32(1))) && (subj[(pos + uint32(1))] == uint8(10))) {
			return uint32(2)
		}
		return uint32(1)
	}
	if (nltype == uint32(4)) {
		if ((tmp2 == uint8(11)) || ((tmp2 == uint8(12)) || (tmp2 == uint8(133)))) {
			return uint32(1)
		}
	}
	return uint32(0)
}

func newline_before(subj []byte, pos uint32, nltype uint32) uint32 {
	if (pos == uint32(0)) {
		return uint32(0)
	}
	if (nltype == uint32(0)) {
		if (subj[(pos - uint32(1))] == uint8(10)) {
			return uint32(1)
		}
		return uint32(0)
	}
	if (nltype == uint32(1)) {
		if (subj[(pos - uint32(1))] == uint8(13)) {
			return uint32(1)
		}
		return uint32(0)
	}
	if (nltype == uint32(2)) {
		if ((pos >= uint32(2)) && ((subj[(pos - uint32(2))] == uint8(13)) && (subj[(pos - uint32(1))] == uint8(10)))) {
			return uint32(2)
		}
		return uint32(0)
	}
	var tmp1 uint8 = subj[(pos - uint32(1))]
	if (tmp1 == uint8(10)) {
		if ((pos >= uint32(2)) && (subj[(pos - uint32(2))] == uint8(13))) {
			return uint32(2)
		}
		return uint32(1)
	}
	if (tmp1 == uint8(13)) {
		return uint32(1)
	}
	if (nltype == uint32(4)) {
		if ((tmp1 == uint8(11)) || ((tmp1 == uint8(12)) || (tmp1 == uint8(133)))) {
			return uint32(1)
		}
	}
	return uint32(0)
}

func note_element(w *Work, lo uint32, hi uint32, ranged bool) {
	if (ranged && (lo != hi)) {
		(*w).clsrange = uint32(1)
	} else {
		(*w).clselems = ((*w).clselems + uint32(1))
	}
	if (((uint8(lo) == uint8(13)) || (uint8(lo) == uint8(10))) || ((uint8(hi) == uint8(13)) || (uint8(hi) == uint8(10)))) {
		(*w).clscrlf = uint32(1)
	}
}

func note_ref(w *Work, num uint32, off uint32, nlen uint32) {
	if (uint32(len((*w).refs)) >= uint32(2048)) {
		(*w).err = uint32(1002)
		return
	}
	tir_push(&(*w).refs, 2048, (Ref{num: num, off: off, nlen: nlen}))
}

func open_group(pat []byte, at *uint32, w *Work) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = ((*at) + uint32(1))
	var tmp3 uint32 = (*at)
	if (((tmp2 < tmp1) && (pat[tmp2] == uint8(42))) && ((tmp1 > (tmp2 + uint32(1))) && (pat[(tmp2 + uint32(1))] != uint8(41)))) {
		(*w).err = uint32(1000)
		(*w).erroff = (tmp2 + uint32(1))
		return
	}
	if ((tmp2 >= tmp1) || (pat[tmp2] != uint8(63))) {
		if ((*w).ncap >= uint32(255)) {
			(*w).err = uint32(1002)
			return
		}
		var tmp4 uint32 = ((*w).ncap + uint32(1))
		(*w).ncap = tmp4
		var tmp5 uint32 = (*w).opts
		push_frame(w, tmp4, tmp5, tmp3, uint32(0))
		(*at) = tmp2
		return
	}
	var tmp6 uint32 = (tmp2 + uint32(1))
	if (tmp6 >= tmp1) {
		(*w).err = uint32(114)
		(*w).erroff = tmp1
		return
	}
	var tmp7 uint8 = pat[tmp6]
	if (tmp7 == uint8(35)) {
		var tmp8 uint32 = (tmp6 + uint32(1))
		for ((tmp8 < tmp1) && (pat[tmp8] != uint8(41))) {
			tmp8 = (tmp8 + uint32(1))
		}
		if (tmp8 >= tmp1) {
			(*w).err = uint32(118)
			(*w).erroff = tmp1
			return
		}
		(*at) = (tmp8 + uint32(1))
		return
	}
	if (tmp7 == uint8(58)) {
		var tmp9 uint32 = (*w).opts
		push_frame(w, uint32(0), tmp9, tmp3, uint32(0))
		(*at) = (tmp6 + uint32(1))
		return
	}
	var tmp10 uint32 = uint32(0)
	if (((((tmp7 == uint8(61)) || (tmp7 == uint8(33))) || (tmp7 == uint8(62))) || (tmp7 == uint8(124))) || (tmp7 == uint8(42))) {
		tmp10 = (tmp6 + uint32(1))
	}
	if ((tmp7 == uint8(60)) && ((tmp1 > (tmp6 + uint32(1))) && (((pat[(tmp6 + uint32(1))] == uint8(61)) || (pat[(tmp6 + uint32(1))] == uint8(33))) || (pat[(tmp6 + uint32(1))] == uint8(42))))) {
		tmp10 = (tmp6 + uint32(2))
	}
	if (tmp10 != uint32(0)) {
		var tmp11 uint32 = (*w).opts
		push_frame(w, uint32(0), tmp11, tmp3, tmp10)
		(*at) = tmp10
		return
	}
	var tmp12 bool = false
	var tmp13 uint8 = uint8(62)
	var tmp14 uint32 = uint32(0)
	if (tmp7 == uint8(60)) {
		tmp12 = true
		tmp14 = (tmp6 + uint32(1))
	}
	if (tmp7 == uint8(39)) {
		tmp12 = true
		tmp13 = uint8(39)
		tmp14 = (tmp6 + uint32(1))
	}
	if ((tmp7 == uint8(80)) && ((tmp1 > (tmp6 + uint32(1))) && (pat[(tmp6 + uint32(1))] == uint8(60)))) {
		tmp12 = true
		tmp14 = (tmp6 + uint32(2))
	}
	if tmp12 {
		named_group(pat, at, w, tmp14, tmp13, tmp3)
		return
	}
	if (((((((tmp7 == uint8(38)) || (tmp7 == uint8(43))) || (tmp7 == uint8(82))) || (tmp7 == uint8(80))) || (tmp7 == uint8(67))) || (tmp7 == uint8(40))) || (tmp7 == uint8(91))) {
		(*w).err = uint32(1000)
		(*w).erroff = (tmp6 + uint32(1))
		return
	}
	var tmp15 bool = false
	tir_t1 := ct(tmp7, uint8(4))
	tmp15 = tir_t1
	if ((tmp7 == uint8(45)) && (tmp1 > (tmp6 + uint32(1)))) {
		tir_t2 := ct(pat[(tmp6 + uint32(1))], uint8(4))
		tmp15 = tir_t2
		if tmp15 {
			(*w).err = uint32(1000)
			(*w).erroff = (tmp6 + uint32(2))
			return
		}
		tmp15 = false
	}
	if tmp15 {
		(*w).err = uint32(1000)
		(*w).erroff = (tmp6 + uint32(1))
		return
	}
	var tmp16 uint32 = uint32(0)
	var tmp17 uint32 = uint32(0)
	var tmp18 bool = false
	var tmp19 bool = true
	var tmp20 bool = false
	var tmp21 bool = false
	var tmp22 uint32 = tmp6
	tir_loop1:
	for (tmp22 < tmp1) {
		var tmp23 uint8 = pat[tmp22]
		if (tmp23 == uint8(45)) {
			if (tmp18 || tmp21) {
				(*w).err = uint32(194)
				(*w).erroff = (tmp22 + uint32(1))
				return
			}
			tmp18 = true
			tmp22 = (tmp22 + uint32(1))
			continue tir_loop1
		}
		var tmp24 uint32 = uint32(0)
		if (tmp23 == uint8(105)) {
			tmp24 = uint32(1)
		}
		if (tmp23 == uint8(109)) {
			tmp24 = uint32(2)
		}
		if (tmp23 == uint8(115)) {
			tmp24 = uint32(4)
		}
		if (tmp23 == uint8(120)) {
			tmp24 = uint32(8)
		}
		if (tmp23 == uint8(85)) {
			tmp24 = uint32(16)
		}
		if (tmp24 == uint32(0)) {
			if (!((((((tmp23 == uint8(97)) || (tmp23 == uint8(74))) || (tmp23 == uint8(110))) || (tmp23 == uint8(114))) || ((tmp23 == uint8(94)) && (tmp22 == tmp6))) || (tmp20 && (((((tmp23 == uint8(68)) || (tmp23 == uint8(80))) || (tmp23 == uint8(83))) || (tmp23 == uint8(84))) || (tmp23 == uint8(87)))))) {
				break tir_loop1
			}
			tmp20 = (tmp23 == uint8(97))
			tmp21 = (tmp23 == uint8(94))
			tmp19 = false
			tmp22 = (tmp22 + uint32(1))
			continue tir_loop1
		}
		tmp20 = false
		tmp21 = false
		if ((tmp23 == uint8(120)) && ((tmp1 > (tmp22 + uint32(1))) && (pat[(tmp22 + uint32(1))] == uint8(120)))) {
			tmp19 = false
		}
		if tmp18 {
			tmp17 = (tmp17 | tmp24)
		} else {
			tmp16 = (tmp16 | tmp24)
		}
		tmp22 = (tmp22 + uint32(1))
	}
	if (tmp22 >= tmp1) {
		(*w).err = uint32(114)
		(*w).erroff = tmp1
		return
	}
	if ((pat[tmp22] != uint8(41)) && (pat[tmp22] != uint8(58))) {
		(*w).err = uint32(111)
		(*w).erroff = (tmp22 + uint32(1))
		return
	}
	if (!tmp19) {
		(*w).err = uint32(1001)
		(*w).erroff = (tmp22 + uint32(1))
		return
	}
	var tmp25 uint32 = (((*w).opts | tmp16) & (^tmp17))
	if (pat[tmp22] == uint8(58)) {
		push_frame(w, uint32(0), tmp25, tmp3, uint32(0))
		(*at) = (tmp22 + uint32(1))
		return
	}
	(*w).opts = tmp25
	var tmp26 uint32 = (uint32(len((*w).frames)) - uint32(1))
	tir_t3 := tmp26
	if tir_t3 >= uint32(len((*w).frames)) {
		tir_oob(tir_t3, uint32(len((*w).frames)))
	}
	(*w).frames[tir_t3].qual = uint32(0)
	(*at) = (tmp22 + uint32(1))
}

func open_region(w *Work, kind Rk, parent uint32) uint32 {
	var tmp1 uint32 = uint32(len((*w).regions))
	if (tmp1 >= uint32(8208)) {
		(*w).err = uint32(1002)
		return uint32(0)
	}
	tir_push(&(*w).regions, 8208, (Region{kind: kind, parent: parent, lo: uint32(len((*w).code)), hi: uint32(len((*w).code))}))
	return tmp1
}

func parse(pat []byte, popts uint32, nltype uint32, w *Work) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = uint32(0)
	_ = tmp2
	tir_t1 := alloc_node(w, NdNil, uint32(0), uint32(0), uint32(0))
	tmp2 = tir_t1
	var tmp3 uint32 = uint32(0)
	tir_t2 := alloc_node(w, NdGroup, uint32(0), uint32(0), uint32(0))
	tmp3 = tir_t2
	var tmp4 uint32 = uint32(0)
	tir_t3 := alloc_node(w, NdConcat, uint32(0), uint32(0), uint32(0))
	tmp4 = tir_t3
	add_child(w, tmp3, tmp4)
	(*w).root = tmp3
	(*w).opts = popts
	(*w).nltype = nltype
	var tmp5 uint32 = popts
	tir_push(&(*w).frames, 251, (Frame{grp: tmp3, alt: uint32(0), cat: tmp4, qual: uint32(0), opts: tmp5, at: uint32(0), unsup: uint32(0)}))
	var tmp6 uint32 = uint32(0)
	var tmp7 bool = false
	var tmp8 bool = false
	var tmp9 Esc
	var tmp10 Quant
	_ = tmp10
	tir_loop1:
	for ((tmp6 < tmp1) && ((*w).err == uint32(0))) {
		var tmp11 uint8 = pat[tmp6]
		if tmp7 {
			if ((tmp11 == uint8(92)) && ((tmp1 > (tmp6 + uint32(1))) && (pat[(tmp6 + uint32(1))] == uint8(69)))) {
				tmp7 = false
				tmp6 = (tmp6 + uint32(2))
				continue tir_loop1
			}
			var tmp12 uint32 = uint32(tmp11)
			add_char(w, tmp12)
			tmp6 = (tmp6 + uint32(1))
			continue tir_loop1
		}
		if (((*w).opts & uint32(8)) != uint32(0)) {
			tir_t4 := ct(tmp11, uint8(2))
			tmp8 = tir_t4
			if (tmp8 || (tmp11 == uint8(35))) {
				skip_gaps(pat, &tmp6, w)
				continue tir_loop1
			}
		}
		if (tmp11 == uint8(40)) {
			open_group(pat, &tmp6, w)
			continue tir_loop1
		}
		if (tmp11 == uint8(41)) {
			if (uint32(len((*w).frames)) <= uint32(1)) {
				(*w).err = uint32(122)
				(*w).erroff = (tmp6 + uint32(1))
				continue tir_loop1
			}
			close_group(w)
			tmp6 = (tmp6 + uint32(1))
			continue tir_loop1
		}
		if (tmp11 == uint8(124)) {
			new_branch(w)
			tmp6 = (tmp6 + uint32(1))
			continue tir_loop1
		}
		if (tmp11 == uint8(91)) {
			if ((tmp1 > (tmp6 + uint32(1))) && (((pat[(tmp6 + uint32(1))] == uint8(58)) || (pat[(tmp6 + uint32(1))] == uint8(46))) || (pat[(tmp6 + uint32(1))] == uint8(61)))) {
				var tmp13 uint32 = uint32(4294967295)
				tir_t5 := posix_end(pat, (tmp6 + uint32(1)))
				tmp13 = tir_t5
				if (tmp13 != uint32(4294967295)) {
					var tmp14 uint32 = uint32(112)
					if (pat[(tmp6 + uint32(1))] != uint8(58)) {
						tmp14 = uint32(113)
					}
					(*w).err = tmp14
					(*w).erroff = (tmp13 + uint32(2))
					continue tir_loop1
				}
			}
			var tmp15 uint32 = uint32(0)
			tir_t6 := parse_class(pat, &tmp6, w)
			tmp15 = tir_t6
			if ((*w).err != uint32(0)) {
				continue tir_loop1
			}
			attach_atom(w, NdClass, tmp15, uint32(0))
			continue tir_loop1
		}
		if (tmp11 == uint8(46)) {
			var tmp16 Nd = NdAnyNoNL
			if (((*w).opts & uint32(4)) != uint32(0)) {
				tmp16 = NdAny
			}
			attach_atom(w, tmp16, uint32(0), uint32(0))
			tmp6 = (tmp6 + uint32(1))
			continue tir_loop1
		}
		if (tmp11 == uint8(94)) {
			var tmp17 Nd = NdCirc
			if (((*w).opts & uint32(2)) != uint32(0)) {
				tmp17 = NdCircM
			}
			attach_atom(w, tmp17, uint32(0), uint32(0))
			tmp6 = (tmp6 + uint32(1))
			continue tir_loop1
		}
		if (tmp11 == uint8(36)) {
			var tmp18 Nd = NdDoll
			if (((*w).opts & uint32(2)) != uint32(0)) {
				tmp18 = NdDollM
			} else {
				if (((*w).opts & uint32(128)) != uint32(0)) {
					tmp18 = NdDollE
				}
			}
			attach_atom(w, tmp18, uint32(0), uint32(0))
			tmp6 = (tmp6 + uint32(1))
			continue tir_loop1
		}
		if ((((tmp11 == uint8(42)) || (tmp11 == uint8(43))) || (tmp11 == uint8(63))) || (tmp11 == uint8(123))) {
			quantifier(pat, &tmp6, w)
			continue tir_loop1
		}
		if (tmp11 == uint8(92)) {
			if (tmp1 > (tmp6 + uint32(1))) {
				var tmp19 uint8 = pat[(tmp6 + uint32(1))]
				if (tmp19 == uint8(81)) {
					tmp7 = true
					tmp6 = (tmp6 + uint32(2))
					continue tir_loop1
				}
				if (tmp19 == uint8(69)) {
					tmp6 = (tmp6 + uint32(2))
					continue tir_loop1
				}
			}
			tir_t7 := read_escape(pat, &tmp6, w, false)
			tmp9 = tir_t7
			if ((*w).err != uint32(0)) {
				continue tir_loop1
			}
			attach_escape(w, tmp9)
			continue tir_loop1
		}
		var tmp20 uint32 = uint32(tmp11)
		add_char(w, tmp20)
		tmp6 = (tmp6 + uint32(1))
	}
	if ((*w).err != uint32(0)) {
		return
	}
	if (uint32(len((*w).frames)) > uint32(1)) {
		(*w).err = uint32(114)
		(*w).erroff = tmp1
		return
	}
	var tmp21 uint32 = uint32(0)
	var tmp22 uint32 = uint32(len((*w).refs))
	var tmp23 bool = false
	for (tmp21 < tmp22) {
		var tmp24 Ref = (*w).refs[tmp21]
		var tmp25 bool = (tmp24.num > (*w).ncap)
		if (tmp24.num == uint32(4294967295)) {
			tir_t8 := name_taken(pat, tmp24.off, tmp24.nlen, w)
			tmp23 = tir_t8
			tmp25 = (!tmp23)
		}
		if tmp25 {
			(*w).err = uint32(115)
			(*w).erroff = tmp24.off
			return
		}
		tmp21 = (tmp21 + uint32(1))
	}
	if (tmp22 > uint32(0)) {
		(*w).err = uint32(1000)
		(*w).erroff = (*w).refs[uint32(0)].off
		return
	}
	check_possess(w)
}

func parse_class(pat []byte, at *uint32, w *Work) uint32 {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = ((*at) + uint32(1))
	var tmp3 bool = false
	var tmp4 bool = false
	class_skip(pat, &tmp2, &tmp4)
	if (((tmp2 < tmp1) && (pat[tmp2] == uint8(94))) && (!tmp4)) {
		tmp3 = true
		tmp2 = (tmp2 + uint32(1))
	}
	var tmp5 uint32 = uint32(0)
	tir_t1 := new_class(w)
	tmp5 = tir_t1
	if ((*w).err != uint32(0)) {
		return uint32(0)
	}
	(*w).clselems = uint32(0)
	(*w).clsrange = uint32(0)
	(*w).clscrlf = uint32(0)
	var tmp6 uint32 = (tmp5 * uint32(32))
	var tmp7 bool = (((*w).opts & uint32(1)) != uint32(0))
	var tmp8 bool = true
	var tmp9 bool = false
	var tmp10 uint32 = uint32(4294967295)
	var tmp11 Esc
	tir_loop1:
	for ((tmp2 < tmp1) && ((*w).err == uint32(0))) {
		var tmp12 uint8 = pat[tmp2]
		if tmp4 {
			if ((tmp12 == uint8(92)) && ((tmp1 > (tmp2 + uint32(1))) && (pat[(tmp2 + uint32(1))] == uint8(69)))) {
				tmp4 = false
				tmp2 = (tmp2 + uint32(2))
				continue tir_loop1
			}
			tmp8 = false
			tmp10 = uint32(tmp12)
			tmp2 = (tmp2 + uint32(1))
			note_element(w, tmp10, tmp10, false)
			set_range(w, tmp6, tmp10, tmp10, tmp7)
			continue tir_loop1
		}
		if ((tmp12 == uint8(93)) && (!tmp8)) {
			tmp2 = (tmp2 + uint32(1))
			tmp9 = true
			break tir_loop1
		}
		if ((tmp12 == uint8(91)) && (tmp1 > (tmp2 + uint32(1)))) {
			var tmp13 uint8 = pat[(tmp2 + uint32(1))]
			if (((tmp13 == uint8(58)) || (tmp13 == uint8(46))) || (tmp13 == uint8(61))) {
				var tmp14 uint32 = uint32(4294967295)
				tir_t2 := posix_end(pat, (tmp2 + uint32(1)))
				tmp14 = tir_t2
				if (tmp14 != uint32(4294967295)) {
					if (tmp13 != uint8(58)) {
						(*w).err = uint32(113)
						(*w).erroff = (tmp14 + uint32(2))
						continue tir_loop1
					}
					tmp8 = false
					(*w).clsrange = uint32(1)
					posix_item(w, pat, tmp2, tmp14, tmp6, tmp7)
					tmp2 = (tmp14 + uint32(2))
					class_after_set(w, tmp2, pat)
					continue tir_loop1
				}
			}
		}
		if (tmp12 == uint8(92)) {
			if (tmp1 > (tmp2 + uint32(1))) {
				var tmp15 uint8 = pat[(tmp2 + uint32(1))]
				if (tmp15 == uint8(81)) {
					tmp4 = true
					tmp2 = (tmp2 + uint32(2))
					continue tir_loop1
				}
				if (tmp15 == uint8(69)) {
					tmp2 = (tmp2 + uint32(2))
					continue tir_loop1
				}
			}
			tmp8 = false
			tir_t3 := read_escape(pat, &tmp2, w, true)
			tmp11 = tir_t3
			if ((*w).err != uint32(0)) {
				continue tir_loop1
			}
			if (tmp11.kind == EkChar) {
				tmp10 = tmp11.val
				class_element(w, &tmp2, &tmp4, pat, tmp6, tmp10, tmp7)
				continue tir_loop1
			}
			var tmp16 uint32 = tmp11.val
			var tmp17 bool = (tmp11.kind == EkNegSet)
			(*w).clsrange = uint32(1)
			set_union(w, tmp6, tmp16, tmp17)
			class_after_set(w, tmp2, pat)
			continue tir_loop1
		}
		tmp8 = false
		tmp10 = uint32(tmp12)
		tmp2 = (tmp2 + uint32(1))
		class_element(w, &tmp2, &tmp4, pat, tmp6, tmp10, tmp7)
	}
	if ((*w).err != uint32(0)) {
		return uint32(0)
	}
	if (!tmp9) {
		(*w).err = uint32(106)
		(*w).erroff = tmp1
		return uint32(0)
	}
	if ((*w).clscrlf != uint32(0)) {
		var tmp18 bool = (tmp3 && (((*w).clselems == uint32(1)) && ((*w).clsrange == uint32(0))))
		if (!tmp18) {
			(*w).hascrlf = uint32(1)
		}
	}
	if tmp3 {
		var tmp19 uint32 = uint32(0)
		for (tmp19 < uint32(32)) {
			var tmp20 uint32 = (tmp6 + tmp19)
			tir_t4 := tmp20
			if tir_t4 >= uint32(len((*w).classes)) {
				tir_oob(tir_t4, uint32(len((*w).classes)))
			}
			(*w).classes[tir_t4] = (^(*w).classes[tmp20])
			tmp19 = (tmp19 + uint32(1))
		}
	}
	(*at) = tmp2
	return tmp5
}

func pike_add(list *[]Th, stk *[]Th, seen *[]byte, pool *[]uint32, rc *[]uint32, free *[]uint32, code []Inst, reps []Rep, subj []byte, pos uint32, novec uint32, nltype uint32, notbol bool, noteol bool, pc0 uint32, h0 uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	var tmp1 uint32 = uint32(len(subj))
	var tmp2 bool = false
	tir_t1 := pike_defer(stk, pc0, h0, mem, peak, cost, memlimit, costlimit)
	tmp2 = tir_t1
	if (!tmp2) {
		return false
	}
	var tmp3 uint64 = tir_cmul(uint64(uint32(len(code))), uint64(2))
	tir_loop1:
	for (uint32(len((*stk))) > uint32(0)) {
		var tmp4 Th
		tmp4 = tir_pop(&(*stk))
		var tmp5 uint32 = tmp4.pc
		var tmp6 uint32 = tmp4.h
		var tmp7 uint32 = (tmp5 >> 3)
		var tmp8 uint8 = BITS[(tmp5 & uint32(7))]
		if (((*seen)[tmp7] & tmp8) != uint8(0)) {
			tir_t2 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t2
			if (!tmp2) {
				return false
			}
			continue tir_loop1
		}
		tir_t3 := tmp7
		if tir_t3 >= uint32(len((*seen))) {
			tir_oob(tir_t3, uint32(len((*seen))))
		}
		(*seen)[tir_t3] = ((*seen)[tmp7] | tmp8)
		tmp3 = tir_csub(tmp3, uint64(2))
		if (uint64(1) > tir_csub(costlimit, (*cost))) {
			return false
		}
		(*cost) = tir_cadd((*cost), uint64(1))
		var tmp9 Inst = code[tmp5]
		switch tmp9.op {
		case OpChar:
			tir_t4 := pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t4
			if (!tmp2) {
				return false
			}
		case OpCharCI:
			tir_t5 := pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t5
			if (!tmp2) {
				return false
			}
		case OpClass:
			tir_t6 := pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t6
			if (!tmp2) {
				return false
			}
		case OpAny:
			tir_t7 := pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t7
			if (!tmp2) {
				return false
			}
		case OpAnyNoNL:
			tir_t8 := pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t8
			if (!tmp2) {
				return false
			}
		case OpAccept:
			tir_t9 := pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t9
			if (!tmp2) {
				return false
			}
		case OpBsr:
			tir_t10 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t10
			if (!tmp2) {
				return false
			}
		case OpSplit:
			tir_t11 := tmp6
			if tir_t11 >= uint32(len((*rc))) {
				tir_oob(tir_t11, uint32(len((*rc))))
			}
			(*rc)[tir_t11] = ((*rc)[tmp6] + uint32(1))
			tir_t12 := pike_defer(stk, tmp9.alt, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t12
			if (!tmp2) {
				return false
			}
			tir_t13 := pike_defer(stk, tmp9.arg, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t13
			if (!tmp2) {
				return false
			}
		case OpJump:
			tir_t14 := pike_defer(stk, tmp9.arg, tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t14
			if (!tmp2) {
				return false
			}
		case OpSave:
			tir_t15 := pike_write(pool, rc, free, novec, &tmp6, tmp9.arg, pos, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t15
			if (!tmp2) {
				return false
			}
			tir_t16 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t16
			if (!tmp2) {
				return false
			}
		case OpCirc:
			if ((pos == uint32(0)) && (!notbol)) {
				tir_t17 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t17
				if (!tmp2) {
					return false
				}
			} else {
				tir_t18 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t18
				if (!tmp2) {
					return false
				}
			}
		case OpCircM:
			var tmp10 bool = (!notbol)
			if (pos != uint32(0)) {
				var tmp11 uint32 = uint32(0)
				tir_t19 := newline_before(subj, pos, nltype)
				tmp11 = tir_t19
				tmp10 = ((pos != tmp1) && (tmp11 != uint32(0)))
			}
			if tmp10 {
				tir_t20 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t20
				if (!tmp2) {
					return false
				}
			} else {
				tir_t21 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t21
				if (!tmp2) {
					return false
				}
			}
		case OpDoll:
			var tmp12 bool = false
			tir_t22 := at_line_end(subj, pos, nltype)
			tmp12 = tir_t22
			if ((!noteol) && tmp12) {
				tir_t23 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t23
				if (!tmp2) {
					return false
				}
			} else {
				tir_t24 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t24
				if (!tmp2) {
					return false
				}
			}
		case OpDollE:
			if ((!noteol) && (pos == tmp1)) {
				tir_t25 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t25
				if (!tmp2) {
					return false
				}
			} else {
				tir_t26 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t26
				if (!tmp2) {
					return false
				}
			}
		case OpDollM:
			var tmp13 bool = (!noteol)
			if (pos < tmp1) {
				var tmp14 uint32 = uint32(0)
				tir_t27 := newline_at(subj, pos, nltype)
				tmp14 = tir_t27
				tmp13 = (tmp14 != uint32(0))
			}
			if tmp13 {
				tir_t28 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t28
				if (!tmp2) {
					return false
				}
			} else {
				tir_t29 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t29
				if (!tmp2) {
					return false
				}
			}
		case OpSod:
			if (pos == uint32(0)) {
				tir_t30 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t30
				if (!tmp2) {
					return false
				}
			} else {
				tir_t31 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t31
				if (!tmp2) {
					return false
				}
			}
		case OpEod:
			if (pos == tmp1) {
				tir_t32 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t32
				if (!tmp2) {
					return false
				}
			} else {
				tir_t33 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t33
				if (!tmp2) {
					return false
				}
			}
		case OpEodn:
			var tmp15 bool = false
			tir_t34 := at_line_end(subj, pos, nltype)
			tmp15 = tir_t34
			if tmp15 {
				tir_t35 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t35
				if (!tmp2) {
					return false
				}
			} else {
				tir_t36 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t36
				if (!tmp2) {
					return false
				}
			}
		case OpWordB:
			tir_t37 := word_edge(subj, pos)
			tmp2 = tir_t37
			if tmp2 {
				tir_t38 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t38
				if (!tmp2) {
					return false
				}
			} else {
				tir_t39 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t39
				if (!tmp2) {
					return false
				}
			}
		case OpNotWordB:
			tir_t40 := word_edge(subj, pos)
			tmp2 = tir_t40
			if (!tmp2) {
				tir_t41 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t41
				if (!tmp2) {
					return false
				}
			} else {
				tir_t42 := pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t42
				if (!tmp2) {
					return false
				}
			}
		case OpRepZero:
			tir_t43 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t43
			if (!tmp2) {
				return false
			}
		case OpRepEnter:
			tir_t44 := pike_defer(stk, (tmp5 + uint32(1)), tmp6, mem, peak, cost, memlimit, costlimit)
			tmp2 = tir_t44
			if (!tmp2) {
				return false
			}
		case OpRepLoop:
			var tmp16 Rep = reps[tmp9.arg]
			if tmp16.greedy {
				tir_t45 := tmp6
				if tir_t45 >= uint32(len((*rc))) {
					tir_oob(tir_t45, uint32(len((*rc))))
				}
				(*rc)[tir_t45] = ((*rc)[tmp6] + uint32(1))
				tir_t46 := pike_defer(stk, tmp16.after, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t46
				if (!tmp2) {
					return false
				}
				tir_t47 := pike_defer(stk, tmp16.body, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t47
				if (!tmp2) {
					return false
				}
			} else {
				tir_t48 := tmp6
				if tir_t48 >= uint32(len((*rc))) {
					tir_oob(tir_t48, uint32(len((*rc))))
				}
				(*rc)[tir_t48] = ((*rc)[tmp6] + uint32(1))
				tir_t49 := pike_defer(stk, tmp16.body, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t49
				if (!tmp2) {
					return false
				}
				tir_t50 := pike_defer(stk, tmp16.after, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t50
				if (!tmp2) {
					return false
				}
			}
		case OpRepNext:
			var tmp17 Rep = reps[tmp9.arg]
			if tmp17.greedy {
				tir_t51 := tmp6
				if tir_t51 >= uint32(len((*rc))) {
					tir_oob(tir_t51, uint32(len((*rc))))
				}
				(*rc)[tir_t51] = ((*rc)[tmp6] + uint32(1))
				tir_t52 := pike_defer(stk, tmp17.after, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t52
				if (!tmp2) {
					return false
				}
				tir_t53 := pike_defer(stk, tmp17.body, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t53
				if (!tmp2) {
					return false
				}
			} else {
				tir_t54 := tmp6
				if tir_t54 >= uint32(len((*rc))) {
					tir_oob(tir_t54, uint32(len((*rc))))
				}
				(*rc)[tir_t54] = ((*rc)[tmp6] + uint32(1))
				tir_t55 := pike_defer(stk, tmp17.body, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t55
				if (!tmp2) {
					return false
				}
				tir_t56 := pike_defer(stk, tmp17.after, tmp6, mem, peak, cost, memlimit, costlimit)
				tmp2 = tir_t56
				if (!tmp2) {
					return false
				}
			}
		}
	}
	return true
}

func pike_check(re Re, cert Cert) Cr {
	var tmp1 bool = false
	tir_t1 := pike_ok(re)
	tmp1 = tir_t1
	if (!tmp1) {
		return CrIneligible
	}
	if (cert.config != CfgPike) {
		return CrConfig
	}
	if (uint32(len(cert.prices)) != uint32(0)) {
		return CrPrices
	}
	var tmp2 bool = false
	switch cert.complexity {
	case CcLinear:
		tmp2 = true
	case CcNotProvenLinear:
		return CrNotLinear
	}
	if (!tmp2) {
		return CrShape
	}
	if (!((((cert.cost.base == uint64(1)) && (cert.cost.c2 == uint64(0))) && (cert.cost.c3 == uint64(0))) && (cert.cost.c4 == uint64(0)))) {
		return CrNotLinear
	}
	var needed Cert
	var tmp3 bool = false
	tir_t2 := pike_price(re, &needed)
	tmp3 = tir_t2
	if (!tmp3) {
		return CrOverflow
	}
	var tmp4 bool = false
	tir_t3 := poly_ge(cert.cost, needed.cost)
	tmp4 = tir_t3
	if (!tmp4) {
		return CrTotalCost
	}
	tir_t4 := poly_eq(cert.stack, needed.stack)
	tmp4 = tir_t4
	if (!tmp4) {
		return CrTotalStack
	}
	tir_t5 := poly_eq(cert.trail, needed.trail)
	tmp4 = tir_t5
	if (!tmp4) {
		return CrTotalTrail
	}
	tir_t6 := poly_ge(cert.mem, needed.mem)
	tmp4 = tir_t6
	if (!tmp4) {
		return CrTotalMem
	}
	return CrOk
}

func pike_defer(held *[]Th, pcv uint32, hv uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	var tmp1 bool = false
	tir_t1 := charge_grow(uint32(cap((*held))), uint32(len((*held))), uint32(8), uint32(131396), mem, peak, cost, memlimit, costlimit)
	tmp1 = tir_t1
	if (!tmp1) {
		return false
	}
	tir_push(&(*held), 131396, (Th{pc: pcv, h: hv}))
	return true
}

func pike_drop(rc *[]uint32, free *[]uint32, h uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	if (h == uint32(4294967295)) {
		return true
	}
	var tmp1 uint32 = ((*rc)[h] - uint32(1))
	tir_t1 := h
	if tir_t1 >= uint32(len((*rc))) {
		tir_oob(tir_t1, uint32(len((*rc))))
	}
	(*rc)[tir_t1] = tmp1
	if (tmp1 == uint32(0)) {
		var tmp2 bool = false
		tir_t2 := charge_grow(uint32(cap((*free))), uint32(len((*free))), uint32(4), uint32(262796), mem, peak, cost, memlimit, costlimit)
		tmp2 = tir_t2
		if (!tmp2) {
			return false
		}
		tir_push(&(*free), 262796, h)
	}
	return true
}

func pike_hollow(re Re, which uint32) bool {
	var tmp1 Rep = re.reps[which]
	var tmp2 uint32 = (tmp1.after - uint32(1))
	var tmp3 uint32 = uint32(len(re.code))
	var seen []byte
	var tmp4 uint32 = ((tmp3 >> 3) + uint32(1))
	var tmp5 uint32 = uint32(0)
	tir_reserve(&seen, tmp4, 2147483647)
	for (tmp5 < tmp4) {
		tir_push(&seen, 2147483647, uint8(0))
		tmp5 = (tmp5 + uint32(1))
	}
	var pending []uint32
	tir_push(&pending, 131396, tmp1.body)
	var tmp6 uint64 = tir_cmul(uint64(tmp3), uint64(2))
	tir_loop1:
	for (uint32(len(pending)) > uint32(0)) {
		var tmp7 uint32 = uint32(0)
		tmp7 = tir_pop(&pending)
		if (tmp7 >= tmp3) {
			return true
		}
		if (tmp7 == tmp2) {
			return true
		}
		var tmp8 uint32 = (tmp7 >> 3)
		var tmp9 uint8 = BITS[(tmp7 & uint32(7))]
		if ((seen[tmp8] & tmp9) != uint8(0)) {
			continue tir_loop1
		}
		tir_t1 := tmp8
		if tir_t1 >= uint32(len(seen)) {
			tir_oob(tir_t1, uint32(len(seen)))
		}
		seen[tir_t1] = (seen[tmp8] | tmp9)
		tmp6 = tir_csub(tmp6, uint64(2))
		var tmp10 Inst = re.code[tmp7]
		switch tmp10.op {
		case OpChar:
		case OpCharCI:
		case OpClass:
		case OpAny:
		case OpAnyNoNL:
		case OpBsr:
		case OpAccept:
		case OpSplit:
			tir_push(&pending, 131396, tmp10.arg)
			tir_push(&pending, 131396, tmp10.alt)
		case OpJump:
			tir_push(&pending, 131396, tmp10.arg)
		case OpRepLoop:
			var tmp11 Rep = re.reps[tmp10.arg]
			tir_push(&pending, 131396, tmp11.body)
			tir_push(&pending, 131396, tmp11.after)
		case OpRepNext:
			var tmp12 Rep = re.reps[tmp10.arg]
			tir_push(&pending, 131396, tmp12.head)
			tir_push(&pending, 131396, tmp12.after)
		default:
			tir_push(&pending, 131396, (tmp7 + uint32(1)))
		}
	}
	return false
}

func pike_match(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ov *[]uint32, use *Usage) uint32 {
	var clist []Th
	_ = clist
	var nlist []Th
	_ = nlist
	var stk []Th
	_ = stk
	var seen []byte
	_ = seen
	var pool []uint32
	_ = pool
	var rc []uint32
	_ = rc
	var free []uint32
	_ = free
	var tmp1 uint32 = uint32(1)
	tir_t1 := pike_run(re, subj, start, mopts, costlimit, stacklimit, memlimit, &clist, &nlist, &stk, &seen, &pool, &rc, &free, ov, use)
	tmp1 = tir_t1
	return tmp1
}

func pike_ok(re Re) bool {
	var tmp1 uint32 = uint32(0)
	for (tmp1 < uint32(len(re.reps))) {
		var tmp2 Rep = re.reps[tmp1]
		if ((tmp2.lo != uint32(0)) || (tmp2.hi != uint32(4294967295))) {
			return false
		}
		var tmp3 bool = true
		tir_t1 := pike_hollow(re, tmp1)
		tmp3 = tir_t1
		if tmp3 {
			return false
		}
		tmp1 = (tmp1 + uint32(1))
	}
	var tmp4 uint32 = uint32(0)
	for (tmp4 < uint32(len(re.code))) {
		if (re.code[tmp4].op == OpBsr) {
			return false
		}
		tmp4 = (tmp4 + uint32(1))
	}
	return true
}

func pike_park(held *[]Th, pcv uint32, hv uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	var tmp1 bool = false
	tir_t1 := charge_grow(uint32(cap((*held))), uint32(len((*held))), uint32(8), uint32(65700), mem, peak, cost, memlimit, costlimit)
	tmp1 = tir_t1
	if (!tmp1) {
		return false
	}
	tir_push(&(*held), 65700, (Th{pc: pcv, h: hv}))
	return true
}

func pike_price(re Re, cert *Cert) bool {
	var over bool = false
	var tmp1 uint64 = uint64(uint32(len(re.code)))
	var tmp2 uint64 = tir_cmul(uint64((re.ncap + uint32(1))), uint64(2))
	var tmp3 uint64 = tir_cmul(tmp2, uint64(4))
	var tmp4 uint64 = uint64(0)
	var tmp5 uint32 = uint32(0)
	for (tmp5 < uint32(len(re.code))) {
		if (re.code[tmp5].op == OpSave) {
			tmp4 = tir_cadd(tmp4, uint64(1))
		}
		tmp5 = (tmp5 + uint32(1))
	}
	var room Room
	pike_room(re, &room, &over)
	var tmp6 uint64 = room.reserved
	var tmp7 uint64 = uint64(room.words)
	var tmp8 uint64
	tir_t1 := sat_add(tmp3, tmp7, &over)
	tmp8 = tir_t1
	var tmp9 uint64
	tir_t2 := sat_mul(tmp1, uint64(2), &over)
	tmp9 = tir_t2
	var tmp10 uint64
	tir_t3 := sat_add(tmp4, uint64(2), &over)
	tmp10 = tir_t3
	var tmp11 uint64
	tir_t4 := sat_mul(tmp10, tmp3, &over)
	tmp11 = tir_t4
	var tmp12 uint64
	tir_t5 := sat_add(tmp9, tmp11, &over)
	tmp12 = tir_t5
	tmp9 = tmp12
	var tmp13 uint64
	tir_t6 := sat_add(tmp9, tmp7, &over)
	tmp13 = tir_t6
	tmp9 = tmp13
	var tmp14 uint64
	tir_t7 := sat_add(tmp8, tmp3, &over)
	tmp14 = tir_t7
	var tmp15 uint64
	tir_t8 := sat_mul(tmp6, uint64(3), &over)
	tmp15 = tir_t8
	var tmp16 uint64
	tir_t9 := sat_add(tmp14, tmp15, &over)
	tmp16 = tir_t9
	var tmp17 uint64
	tir_t10 := sat_mul(tmp6, uint64(2), &over)
	tmp17 = tir_t10
	var tmp18 uint64
	tir_t11 := sat_add(tmp14, tmp17, &over)
	tmp18 = tir_t11
	if over {
		return false
	}
	(*cert).config = CfgPike
	(*cert).complexity = CcLinear
	(*cert).cost = (Poly{base: uint64(1), c0: tmp16, c1: tmp9, c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*cert).stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*cert).trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*cert).mem = (Poly{base: uint64(1), c0: tmp18, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	var empty []Price
	_ = empty
	(*cert).prices = empty
	empty = nil
	return true
}

func pike_room(re Re, room *Room, over *bool) {
	var tmp1 uint64 = uint64(uint32(len(re.code)))
	var tmp2 uint64 = tir_cmul(uint64((re.ncap + uint32(1))), uint64(2))
	(*room).words = ((uint32(len(re.code)) >> 3) + uint32(1))
	var tmp3 uint64 = uint64(0)
	if (tmp1 > uint64(0)) {
		var tmp4 uint64
		tir_t1 := sat_mul(tmp1, uint64(2), over)
		tmp4 = tir_t1
		var tmp5 uint64
		tir_t2 := sat_add(tmp4, uint64(4), over)
		tmp5 = tir_t2
		tmp3 = tmp5
	}
	(*room).lists = tmp3
	var tmp6 uint64
	tir_t3 := sat_mul(tmp1, uint64(2), over)
	tmp6 = tir_t3
	var tmp7 uint64 = uint64(0)
	if (tmp6 > uint64(0)) {
		var tmp8 uint64
		tir_t4 := sat_mul(tmp6, uint64(2), over)
		tmp8 = tir_t4
		var tmp9 uint64
		tir_t5 := sat_add(tmp8, uint64(4), over)
		tmp9 = tir_t5
		tmp7 = tmp9
	}
	(*room).stk = tmp7
	var tmp10 uint64
	tir_t6 := sat_mul(tmp1, uint64(4), over)
	tmp10 = tir_t6
	var tmp11 uint64
	tir_t7 := sat_add(tmp10, uint64(2), over)
	tmp11 = tir_t7
	var tmp12 uint64 = tmp11
	var tmp13 uint64 = uint64(0)
	if (tmp12 > uint64(0)) {
		var tmp14 uint64
		tir_t8 := sat_mul(tmp12, uint64(2), over)
		tmp14 = tir_t8
		var tmp15 uint64
		tir_t9 := sat_add(tmp14, uint64(4), over)
		tmp15 = tir_t9
		tmp13 = tmp15
	}
	(*room).tables = tmp13
	var tmp16 uint64
	tir_t10 := sat_mul(tmp12, tmp2, over)
	tmp16 = tir_t10
	var tmp17 uint64 = uint64(0)
	if (tmp16 > uint64(0)) {
		var tmp18 uint64
		tir_t11 := sat_mul(tmp16, uint64(2), over)
		tmp18 = tir_t11
		var tmp19 uint64
		tir_t12 := sat_add(tmp18, uint64(4), over)
		tmp19 = tir_t12
		tmp17 = tmp19
	}
	(*room).pool = tmp17
	var tmp20 uint64
	tir_t13 := sat_mul((*room).lists, uint64(16), over)
	tmp20 = tir_t13
	var tmp21 uint64 = tmp20
	var tmp22 uint64
	tir_t14 := sat_mul((*room).stk, uint64(8), over)
	tmp22 = tir_t14
	var tmp23 uint64
	tir_t15 := sat_add(tmp21, tmp22, over)
	tmp23 = tir_t15
	tmp21 = tmp23
	var tmp24 uint64
	tir_t16 := sat_mul((*room).tables, uint64(8), over)
	tmp24 = tir_t16
	var tmp25 uint64
	tir_t17 := sat_add(tmp21, tmp24, over)
	tmp25 = tir_t17
	tmp21 = tmp25
	var tmp26 uint64
	tir_t18 := sat_mul((*room).pool, uint64(4), over)
	tmp26 = tir_t18
	var tmp27 uint64
	tir_t19 := sat_add(tmp21, tmp26, over)
	tmp27 = tir_t19
	tmp21 = tmp27
	(*room).reserved = tmp21
}

func pike_run(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, clist *[]Th, nlist *[]Th, stk *[]Th, seen *[]byte, pool *[]uint32, rc *[]uint32, free *[]uint32, ov *[]uint32, use *Usage) uint32 {
	var tmp1 uint32 = uint32(len(subj))
	var tmp2 uint64 = uint64(0)
	var tmp3 uint64 = uint64(0)
	_ = tmp3
	var tmp4 uint64 = uint64(0)
	(*use).cost = tmp2
	(*use).stack = uint32(0)
	(*use).mem = tmp4
	if (!re.pike) {
		return uint32(3)
	}
	if (start > tmp1) {
		return uint32(3)
	}
	var code []Inst = re.code
	var reps []Rep = re.reps
	var classes []byte = re.classes
	var tmp5 uint32 = re.nltype
	var tmp6 uint32 = re.ncap
	var tmp7 uint32 = ((tmp6 + uint32(1)) * uint32(2))
	var tmp8 bool = (((re.opts & uint32(32)) != uint32(0)) || ((mopts & uint32(16)) != uint32(0)))
	var tmp9 bool = ((mopts & uint32(4)) != uint32(0))
	var tmp10 bool = ((mopts & uint32(8)) != uint32(0))
	var tmp11 bool = (re.hascrlf == uint32(0))
	var tmp12 bool = ((tmp5 == uint32(2)) || ((tmp5 == uint32(3)) || (tmp5 == uint32(4))))
	var tmp13 bool = ((mopts & uint32(1)) != uint32(0))
	var tmp14 bool = ((mopts & uint32(2)) != uint32(0))
	tir_truncate(&(*clist), uint32(0))
	tir_truncate(&(*nlist), uint32(0))
	tir_truncate(&(*stk), uint32(0))
	tir_truncate(&(*seen), uint32(0))
	tir_truncate(&(*pool), uint32(0))
	tir_truncate(&(*rc), uint32(0))
	tir_truncate(&(*free), uint32(0))
	var tmp15 uint32 = ((uint32(len(code)) >> 3) + uint32(1))
	var tmp16 uint64 = tir_cadd(tir_cmul(uint64(tmp7), uint64(4)), uint64(tmp15))
	if ((tmp16 > memlimit) || (tmp16 > costlimit)) {
		return uint32(2)
	}
	tmp3 = tmp16
	tmp4 = tmp16
	tmp2 = tmp16
	tir_reserve(&(*ov), tmp7, 512)
	tir_truncate(&(*ov), uint32(0))
	var tmp17 uint32 = uint32(0)
	for (tmp17 < tmp7) {
		tir_push(&(*ov), 512, uint32(4294967295))
		tmp17 = (tmp17 + uint32(1))
	}
	tir_reserve(&(*seen), tmp15, 2147483647)
	tmp17 = uint32(0)
	for (tmp17 < tmp15) {
		tir_push(&(*seen), 2147483647, uint8(0))
		tmp17 = (tmp17 + uint32(1))
	}
	var tmp18 uint32 = uint32(4294967295)
	var tmp19 bool = true
	var tmp20 uint32 = uint32(1)
	var tmp21 bool = true
	var tmp22 uint32 = start
	var tmp23 bool = false
	var tmp24 uint64 = tir_cmul(uint64(tmp7), uint64(4))
	var tmp25 uint64 = uint64(tmp15)
	var tmp26 bool = (re.crfirst != uint32(0))
	for tmp21 {
		if (tmp19 && ((!tmp8) || (tmp22 == start))) {
			var tmp27 bool = false
			if ((tmp22 > start) && (tmp12 && tmp11)) {
				if (tmp26 && ((subj[(tmp22 - uint32(1))] == uint8(13)) && ((tmp22 < tmp1) && (subj[tmp22] == uint8(10))))) {
					tmp27 = true
				}
			}
			if (!tmp27) {
				var tmp28 uint32 = uint32(4294967295)
				tir_t1 := pike_take(pool, rc, free, tmp7, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
				tmp28 = tir_t1
				if (tmp28 == uint32(4294967295)) {
					tmp20 = uint32(2)
					tmp21 = false
				} else {
					if (tmp24 > tir_csub(costlimit, tmp2)) {
						tmp20 = uint32(2)
						tmp21 = false
					} else {
						tmp2 = tir_cadd(tmp2, tmp24)
						var tmp29 uint32 = (tmp28 * tmp7)
						tmp17 = uint32(0)
						for (tmp17 < tmp7) {
							tir_t2 := (tmp29 + tmp17)
							if tir_t2 >= uint32(len((*pool))) {
								tir_oob(tir_t2, uint32(len((*pool))))
							}
							(*pool)[tir_t2] = uint32(4294967295)
							tmp17 = (tmp17 + uint32(1))
						}
						tir_t3 := tmp29
						if tir_t3 >= uint32(len((*pool))) {
							tir_oob(tir_t3, uint32(len((*pool))))
						}
						(*pool)[tir_t3] = tmp22
						tir_t4 := pike_add(clist, stk, seen, pool, rc, free, code, reps, subj, tmp22, tmp7, tmp5, tmp13, tmp14, uint32(0), tmp28, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
						tmp23 = tir_t4
						if (!tmp23) {
							tmp20 = uint32(2)
							tmp21 = false
						}
					}
				}
			}
		}
		if tmp21 {
			if (tmp25 > tir_csub(costlimit, tmp2)) {
				tmp20 = uint32(2)
				tmp21 = false
			} else {
				tmp2 = tir_cadd(tmp2, tmp25)
				tmp17 = uint32(0)
				for (tmp17 < tmp15) {
					tir_t5 := tmp17
					if tir_t5 >= uint32(len((*seen))) {
						tir_oob(tir_t5, uint32(len((*seen))))
					}
					(*seen)[tir_t5] = uint8(0)
					tmp17 = (tmp17 + uint32(1))
				}
			}
		}
		var tmp30 uint32 = uint32(0)
		tir_loop1:
		for (tmp21 && (tmp30 < uint32(len((*clist))))) {
			var tmp31 Th = (*clist)[tmp30]
			var tmp32 uint32 = tmp31.pc
			var tmp33 uint32 = tmp31.h
			if (uint64(1) > tir_csub(costlimit, tmp2)) {
				tmp20 = uint32(2)
				tmp21 = false
				continue tir_loop1
			}
			tmp2 = tir_cadd(tmp2, uint64(1))
			var tmp34 Inst = code[tmp32]
			switch tmp34.op {
			case OpChar:
				if ((tmp22 < tmp1) && (subj[tmp22] == uint8(tmp34.arg))) {
					tir_t6 := pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, (tmp22 + uint32(1)), tmp7, tmp5, tmp13, tmp14, (tmp32 + uint32(1)), tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t6
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				} else {
					tir_t7 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t7
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				}
			case OpCharCI:
				if ((tmp22 < tmp1) && (LOWER[uint32(subj[tmp22])] == uint8(tmp34.arg))) {
					tir_t8 := pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, (tmp22 + uint32(1)), tmp7, tmp5, tmp13, tmp14, (tmp32 + uint32(1)), tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t8
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				} else {
					tir_t9 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t9
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				}
			case OpClass:
				var tmp35 bool = false
				if (tmp22 < tmp1) {
					tir_t10 := class_has(classes, tmp34.arg, subj[tmp22])
					tmp35 = tir_t10
				}
				if ((tmp22 < tmp1) && tmp35) {
					tir_t11 := pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, (tmp22 + uint32(1)), tmp7, tmp5, tmp13, tmp14, (tmp32 + uint32(1)), tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t11
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				} else {
					tir_t12 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t12
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				}
			case OpAny:
				if ((tmp22 < tmp1) && true) {
					tir_t13 := pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, (tmp22 + uint32(1)), tmp7, tmp5, tmp13, tmp14, (tmp32 + uint32(1)), tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t13
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				} else {
					tir_t14 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t14
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				}
			case OpAnyNoNL:
				var tmp36 uint32 = uint32(0)
				if (tmp22 < tmp1) {
					tir_t15 := newline_at(subj, tmp22, tmp5)
					tmp36 = tir_t15
				}
				if ((tmp22 < tmp1) && (tmp36 == uint32(0))) {
					tir_t16 := pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, (tmp22 + uint32(1)), tmp7, tmp5, tmp13, tmp14, (tmp32 + uint32(1)), tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t16
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				} else {
					tir_t17 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t17
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				}
			case OpAccept:
				var tmp37 uint32 = (*pool)[(tmp33 * tmp7)]
				var tmp38 bool = (tmp37 == tmp22)
				var tmp39 bool = (tmp38 && (tmp9 || (tmp10 && (tmp37 == start))))
				if tmp39 {
					tir_t18 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t18
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					}
				} else {
					var tmp40 uint32 = tmp33
					tir_t19 := pike_write(pool, rc, free, tmp7, &tmp40, uint32(1), tmp22, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
					tmp23 = tir_t19
					if (!tmp23) {
						tmp20 = uint32(2)
						tmp21 = false
					} else {
						tir_t20 := pike_drop(rc, free, tmp18, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
						tmp23 = tir_t20
						if (!tmp23) {
							tmp20 = uint32(2)
							tmp21 = false
						}
						if tmp21 {
							tmp18 = tmp40
							tmp19 = false
							tmp20 = uint32(0)
							var tmp41 uint32 = (tmp30 + uint32(1))
							for (tmp21 && (tmp41 < uint32(len((*clist))))) {
								tir_t21 := pike_drop(rc, free, (*clist)[tmp41].h, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
								tmp23 = tir_t21
								if (!tmp23) {
									tmp20 = uint32(2)
									tmp21 = false
								}
								tmp41 = (tmp41 + uint32(1))
							}
							tmp30 = uint32(len((*clist)))
							continue tir_loop1
						}
					}
				}
			default:
				tir_t22 := pike_drop(rc, free, tmp33, &tmp3, &tmp4, &tmp2, memlimit, costlimit)
				tmp23 = tir_t22
				if (!tmp23) {
					tmp20 = uint32(2)
					tmp21 = false
				}
			}
			tmp30 = (tmp30 + uint32(1))
		}
		if tmp21 {
			tir_truncate(&(*clist), uint32(0))
			tir_t23 := (*clist)
			(*clist) = (*nlist)
			(*nlist) = tir_t23
			if (tmp22 >= tmp1) {
				tmp21 = false
			} else {
				if ((uint32(len((*clist))) == uint32(0)) && ((!tmp19) || tmp8)) {
					tmp21 = false
				}
			}
		}
		tmp22 = (tmp22 + uint32(1))
	}
	if (tmp20 == uint32(0)) {
		if (tmp24 > tir_csub(costlimit, tmp2)) {
			tmp20 = uint32(2)
		} else {
			tmp2 = tir_cadd(tmp2, tmp24)
			tmp17 = uint32(0)
			for (tmp17 < tmp7) {
				tir_t24 := tmp17
				if tir_t24 >= uint32(len((*ov))) {
					tir_oob(tir_t24, uint32(len((*ov))))
				}
				(*ov)[tir_t24] = (*pool)[((tmp18 * tmp7) + tmp17)]
				tmp17 = (tmp17 + uint32(1))
			}
		}
	}
	(*use).cost = tmp2
	(*use).stack = uint32(0)
	(*use).mem = tmp4
	return tmp20
}

func pike_take(pool *[]uint32, rc *[]uint32, free *[]uint32, novec uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) uint32 {
	if (uint32(len((*free))) > uint32(0)) {
		var tmp1 uint32 = uint32(0)
		tmp1 = tir_pop(&(*free))
		tir_t1 := tmp1
		if tir_t1 >= uint32(len((*rc))) {
			tir_oob(tir_t1, uint32(len((*rc))))
		}
		(*rc)[tir_t1] = uint32(1)
		return tmp1
	}
	var tmp2 uint32 = uint32(len((*rc)))
	if (tmp2 >= uint32(262796)) {
		return uint32(4294967295)
	}
	var tmp3 bool = false
	tir_t2 := charge_grow(uint32(cap((*rc))), uint32(len((*rc))), uint32(4), uint32(262796), mem, peak, cost, memlimit, costlimit)
	tmp3 = tir_t2
	if (!tmp3) {
		return uint32(4294967295)
	}
	tir_push(&(*rc), 262796, uint32(1))
	var tmp4 uint32 = uint32(0)
	for (tmp4 < novec) {
		tir_t3 := charge_grow(uint32(cap((*pool))), uint32(len((*pool))), uint32(4), uint32(134549508), mem, peak, cost, memlimit, costlimit)
		tmp3 = tir_t3
		if (!tmp3) {
			return uint32(4294967295)
		}
		tir_push(&(*pool), 134549508, uint32(4294967295))
		tmp4 = (tmp4 + uint32(1))
	}
	return tmp2
}

func pike_write(pool *[]uint32, rc *[]uint32, free *[]uint32, novec uint32, h *uint32, slot uint32, value uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	if ((*rc)[(*h)] > uint32(1)) {
		var tmp1 uint64 = tir_cmul(uint64(novec), uint64(4))
		if (tmp1 > tir_csub(costlimit, (*cost))) {
			return false
		}
		(*cost) = tir_cadd((*cost), tmp1)
		var tmp2 uint32 = uint32(4294967295)
		tir_t1 := pike_take(pool, rc, free, novec, mem, peak, cost, memlimit, costlimit)
		tmp2 = tir_t1
		if (tmp2 == uint32(4294967295)) {
			return false
		}
		var tmp3 uint32 = (tmp2 * novec)
		var tmp4 uint32 = ((*h) * novec)
		var tmp5 uint32 = uint32(0)
		for (tmp5 < novec) {
			tir_t2 := (tmp3 + tmp5)
			if tir_t2 >= uint32(len((*pool))) {
				tir_oob(tir_t2, uint32(len((*pool))))
			}
			(*pool)[tir_t2] = (*pool)[(tmp4 + tmp5)]
			tmp5 = (tmp5 + uint32(1))
		}
		tir_t3 := (*h)
		if tir_t3 >= uint32(len((*rc))) {
			tir_oob(tir_t3, uint32(len((*rc))))
		}
		(*rc)[tir_t3] = ((*rc)[(*h)] - uint32(1))
		(*h) = tmp2
	}
	tir_t4 := (((*h) * novec) + slot)
	if tir_t4 >= uint32(len((*pool))) {
		tir_oob(tir_t4, uint32(len((*pool))))
	}
	(*pool)[tir_t4] = value
	return true
}

func poly_add(a Poly, b Poly, over *bool) Poly {
	var out Poly
	out.base = a.base
	if (b.base > a.base) {
		out.base = b.base
	}
	var tmp1 uint64
	tir_t1 := sat_add(a.c0, b.c0, over)
	tmp1 = tir_t1
	out.c0 = tmp1
	var tmp2 uint64
	tir_t2 := sat_add(a.c1, b.c1, over)
	tmp2 = tir_t2
	out.c1 = tmp2
	var tmp3 uint64
	tir_t3 := sat_add(a.c2, b.c2, over)
	tmp3 = tir_t3
	out.c2 = tmp3
	var tmp4 uint64
	tir_t4 := sat_add(a.c3, b.c3, over)
	tmp4 = tir_t4
	out.c3 = tmp4
	var tmp5 uint64
	tir_t5 := sat_add(a.c4, b.c4, over)
	tmp5 = tir_t5
	out.c4 = tmp5
	var done Poly
	tir_t6 := poly_norm(out)
	done = tir_t6
	return done
}

func poly_eq(a Poly, b Poly) bool {
	if (a.base != b.base) {
		return false
	}
	if (a.c0 != b.c0) {
		return false
	}
	if (a.c1 != b.c1) {
		return false
	}
	if (a.c2 != b.c2) {
		return false
	}
	if (a.c3 != b.c3) {
		return false
	}
	if (a.c4 != b.c4) {
		return false
	}
	return true
}

func poly_ge(a Poly, b Poly) bool {
	if (a.base < b.base) {
		return false
	}
	if (a.c0 < b.c0) {
		return false
	}
	if (a.c1 < b.c1) {
		return false
	}
	if (a.c2 < b.c2) {
		return false
	}
	if (a.c3 < b.c3) {
		return false
	}
	if (a.c4 < b.c4) {
		return false
	}
	return true
}

func poly_mul(a Poly, b Poly, over *bool) Poly {
	var out Poly = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	var base uint64
	tir_t1 := sat_mul(a.base, b.base, over)
	base = tir_t1
	out.base = base
	if ((a.c0 != uint64(0)) && (b.c0 != uint64(0))) {
		var tmp1 uint64
		tir_t2 := sat_mul(a.c0, b.c0, over)
		tmp1 = tir_t2
		var tmp2 uint64
		tir_t3 := sat_add(out.c0, tmp1, over)
		tmp2 = tir_t3
		out.c0 = tmp2
	}
	if ((a.c0 != uint64(0)) && (b.c1 != uint64(0))) {
		var tmp3 uint64
		tir_t4 := sat_mul(a.c0, b.c1, over)
		tmp3 = tir_t4
		var tmp4 uint64
		tir_t5 := sat_add(out.c1, tmp3, over)
		tmp4 = tir_t5
		out.c1 = tmp4
	}
	if ((a.c0 != uint64(0)) && (b.c2 != uint64(0))) {
		var tmp5 uint64
		tir_t6 := sat_mul(a.c0, b.c2, over)
		tmp5 = tir_t6
		var tmp6 uint64
		tir_t7 := sat_add(out.c2, tmp5, over)
		tmp6 = tir_t7
		out.c2 = tmp6
	}
	if ((a.c0 != uint64(0)) && (b.c3 != uint64(0))) {
		var tmp7 uint64
		tir_t8 := sat_mul(a.c0, b.c3, over)
		tmp7 = tir_t8
		var tmp8 uint64
		tir_t9 := sat_add(out.c3, tmp7, over)
		tmp8 = tir_t9
		out.c3 = tmp8
	}
	if ((a.c0 != uint64(0)) && (b.c4 != uint64(0))) {
		var tmp9 uint64
		tir_t10 := sat_mul(a.c0, b.c4, over)
		tmp9 = tir_t10
		var tmp10 uint64
		tir_t11 := sat_add(out.c4, tmp9, over)
		tmp10 = tir_t11
		out.c4 = tmp10
	}
	if ((a.c1 != uint64(0)) && (b.c0 != uint64(0))) {
		var tmp11 uint64
		tir_t12 := sat_mul(a.c1, b.c0, over)
		tmp11 = tir_t12
		var tmp12 uint64
		tir_t13 := sat_add(out.c1, tmp11, over)
		tmp12 = tir_t13
		out.c1 = tmp12
	}
	if ((a.c1 != uint64(0)) && (b.c1 != uint64(0))) {
		var tmp13 uint64
		tir_t14 := sat_mul(a.c1, b.c1, over)
		tmp13 = tir_t14
		var tmp14 uint64
		tir_t15 := sat_add(out.c2, tmp13, over)
		tmp14 = tir_t15
		out.c2 = tmp14
	}
	if ((a.c1 != uint64(0)) && (b.c2 != uint64(0))) {
		var tmp15 uint64
		tir_t16 := sat_mul(a.c1, b.c2, over)
		tmp15 = tir_t16
		var tmp16 uint64
		tir_t17 := sat_add(out.c3, tmp15, over)
		tmp16 = tir_t17
		out.c3 = tmp16
	}
	if ((a.c1 != uint64(0)) && (b.c3 != uint64(0))) {
		var tmp17 uint64
		tir_t18 := sat_mul(a.c1, b.c3, over)
		tmp17 = tir_t18
		var tmp18 uint64
		tir_t19 := sat_add(out.c4, tmp17, over)
		tmp18 = tir_t19
		out.c4 = tmp18
	}
	if ((a.c1 != uint64(0)) && (b.c4 != uint64(0))) {
		(*over) = true
	}
	if ((a.c2 != uint64(0)) && (b.c0 != uint64(0))) {
		var tmp19 uint64
		tir_t20 := sat_mul(a.c2, b.c0, over)
		tmp19 = tir_t20
		var tmp20 uint64
		tir_t21 := sat_add(out.c2, tmp19, over)
		tmp20 = tir_t21
		out.c2 = tmp20
	}
	if ((a.c2 != uint64(0)) && (b.c1 != uint64(0))) {
		var tmp21 uint64
		tir_t22 := sat_mul(a.c2, b.c1, over)
		tmp21 = tir_t22
		var tmp22 uint64
		tir_t23 := sat_add(out.c3, tmp21, over)
		tmp22 = tir_t23
		out.c3 = tmp22
	}
	if ((a.c2 != uint64(0)) && (b.c2 != uint64(0))) {
		var tmp23 uint64
		tir_t24 := sat_mul(a.c2, b.c2, over)
		tmp23 = tir_t24
		var tmp24 uint64
		tir_t25 := sat_add(out.c4, tmp23, over)
		tmp24 = tir_t25
		out.c4 = tmp24
	}
	if ((a.c2 != uint64(0)) && (b.c3 != uint64(0))) {
		(*over) = true
	}
	if ((a.c2 != uint64(0)) && (b.c4 != uint64(0))) {
		(*over) = true
	}
	if ((a.c3 != uint64(0)) && (b.c0 != uint64(0))) {
		var tmp25 uint64
		tir_t26 := sat_mul(a.c3, b.c0, over)
		tmp25 = tir_t26
		var tmp26 uint64
		tir_t27 := sat_add(out.c3, tmp25, over)
		tmp26 = tir_t27
		out.c3 = tmp26
	}
	if ((a.c3 != uint64(0)) && (b.c1 != uint64(0))) {
		var tmp27 uint64
		tir_t28 := sat_mul(a.c3, b.c1, over)
		tmp27 = tir_t28
		var tmp28 uint64
		tir_t29 := sat_add(out.c4, tmp27, over)
		tmp28 = tir_t29
		out.c4 = tmp28
	}
	if ((a.c3 != uint64(0)) && (b.c2 != uint64(0))) {
		(*over) = true
	}
	if ((a.c3 != uint64(0)) && (b.c3 != uint64(0))) {
		(*over) = true
	}
	if ((a.c3 != uint64(0)) && (b.c4 != uint64(0))) {
		(*over) = true
	}
	if ((a.c4 != uint64(0)) && (b.c0 != uint64(0))) {
		var tmp29 uint64
		tir_t30 := sat_mul(a.c4, b.c0, over)
		tmp29 = tir_t30
		var tmp30 uint64
		tir_t31 := sat_add(out.c4, tmp29, over)
		tmp30 = tir_t31
		out.c4 = tmp30
	}
	if ((a.c4 != uint64(0)) && (b.c1 != uint64(0))) {
		(*over) = true
	}
	if ((a.c4 != uint64(0)) && (b.c2 != uint64(0))) {
		(*over) = true
	}
	if ((a.c4 != uint64(0)) && (b.c3 != uint64(0))) {
		(*over) = true
	}
	if ((a.c4 != uint64(0)) && (b.c4 != uint64(0))) {
		(*over) = true
	}
	var done Poly
	tir_t32 := poly_norm(out)
	done = tir_t32
	return done
}

func poly_norm(p Poly) Poly {
	if (((((p.c0 == uint64(0)) && (p.c1 == uint64(0))) && (p.c2 == uint64(0))) && (p.c3 == uint64(0))) && (p.c4 == uint64(0))) {
		return (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	}
	return p
}

func poly_value(p Poly, n uint64) Bound {
	if (((((p.c0 == uint64(0)) && (p.c1 == uint64(0))) && (p.c2 == uint64(0))) && (p.c3 == uint64(0))) && (p.c4 == uint64(0))) {
		return (Bound{ok: true, value: uint64(0)})
	}
	var rise Bound
	tir_t1 := bound_add((Bound{ok: true, value: n}), (Bound{ok: true, value: uint64(1)}))
	rise = tir_t1
	var power Bound = (Bound{ok: true, value: uint64(1)})
	var total Bound = (Bound{ok: true, value: p.c0})
	if ((((p.c1 != uint64(0)) || (p.c2 != uint64(0))) || (p.c3 != uint64(0))) || (p.c4 != uint64(0))) {
		var tmp1 Bound
		tir_t2 := bound_mul(power, rise)
		tmp1 = tir_t2
		power = tmp1
		if (p.c1 != uint64(0)) {
			var tmp2 Bound
			tir_t3 := bound_mul((Bound{ok: true, value: p.c1}), power)
			tmp2 = tir_t3
			var tmp3 Bound
			tir_t4 := bound_add(total, tmp2)
			tmp3 = tir_t4
			total = tmp3
		}
	}
	if (((p.c2 != uint64(0)) || (p.c3 != uint64(0))) || (p.c4 != uint64(0))) {
		var tmp4 Bound
		tir_t5 := bound_mul(power, rise)
		tmp4 = tir_t5
		power = tmp4
		if (p.c2 != uint64(0)) {
			var tmp5 Bound
			tir_t6 := bound_mul((Bound{ok: true, value: p.c2}), power)
			tmp5 = tir_t6
			var tmp6 Bound
			tir_t7 := bound_add(total, tmp5)
			tmp6 = tir_t7
			total = tmp6
		}
	}
	if ((p.c3 != uint64(0)) || (p.c4 != uint64(0))) {
		var tmp7 Bound
		tir_t8 := bound_mul(power, rise)
		tmp7 = tir_t8
		power = tmp7
		if (p.c3 != uint64(0)) {
			var tmp8 Bound
			tir_t9 := bound_mul((Bound{ok: true, value: p.c3}), power)
			tmp8 = tir_t9
			var tmp9 Bound
			tir_t10 := bound_add(total, tmp8)
			tmp9 = tir_t10
			total = tmp9
		}
	}
	if (p.c4 != uint64(0)) {
		var tmp10 Bound
		tir_t11 := bound_mul(power, rise)
		tmp10 = tir_t11
		power = tmp10
		if (p.c4 != uint64(0)) {
			var tmp11 Bound
			tir_t12 := bound_mul((Bound{ok: true, value: p.c4}), power)
			tmp11 = tir_t12
			var tmp12 Bound
			tir_t13 := bound_add(total, tmp11)
			tmp12 = tir_t13
			total = tmp12
		}
	}
	var growth Bound
	tir_t14 := bound_pow(p.base, n)
	growth = tir_t14
	var out Bound
	tir_t15 := bound_mul(growth, total)
	out = tir_t15
	return out
}

func posix_end(pat []byte, at uint32) uint32 {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint8 = pat[at]
	var tmp3 uint32 = (at + uint32(1))
	tir_loop1:
	for (tmp1 > (tmp3 + uint32(1))) {
		var tmp4 uint8 = pat[tmp3]
		if ((tmp4 == uint8(92)) && ((pat[(tmp3 + uint32(1))] == uint8(93)) || (pat[(tmp3 + uint32(1))] == uint8(92)))) {
			tmp3 = (tmp3 + uint32(2))
			continue tir_loop1
		}
		if (((tmp4 == uint8(91)) && (pat[(tmp3 + uint32(1))] == tmp2)) || (tmp4 == uint8(93))) {
			return uint32(4294967295)
		}
		if ((tmp4 == tmp2) && (pat[(tmp3 + uint32(1))] == uint8(93))) {
			return tmp3
		}
		tmp3 = (tmp3 + uint32(1))
	}
	return uint32(4294967295)
}

func posix_item(w *Work, pat []byte, at uint32, stop uint32, base uint32, fold bool) {
	var tmp1 uint32 = (at + uint32(2))
	var tmp2 bool = false
	if (pat[tmp1] == uint8(94)) {
		tmp2 = true
		tmp1 = (tmp1 + uint32(1))
	}
	var tmp3 uint32 = uint32(255)
	var tmp4 uint32 = (stop - tmp1)
	tir_t1 := posix_set(pat, tmp1, tmp4)
	tmp3 = tir_t1
	if (tmp3 == uint32(255)) {
		(*w).err = uint32(130)
		(*w).erroff = (stop + uint32(2))
		return
	}
	if fold {
		if ((tmp3 == uint32(11)) || (tmp3 == uint32(14))) {
			tmp3 = uint32(5)
		}
	}
	var tmp5 uint32 = base
	set_union(w, tmp5, tmp3, tmp2)
}

func posix_set(pat []byte, off uint32, nlen uint32) uint32 {
	var tmp1 uint32 = uint32(0)
	var tmp2 uint32 = uint32(len(POSIX))
	for (tmp1 < tmp2) {
		var tmp3 uint32 = uint32(POSIX[tmp1])
		if (tmp3 == nlen) {
			var tmp4 uint32 = uint32(0)
			var tmp5 bool = true
			tir_loop1:
			for (tmp4 < tmp3) {
				if (pat[(off + tmp4)] != POSIX[((tmp1 + uint32(1)) + tmp4)]) {
					tmp5 = false
					break tir_loop1
				}
				tmp4 = (tmp4 + uint32(1))
			}
			if tmp5 {
				return uint32(POSIX[((tmp1 + uint32(1)) + tmp3)])
			}
		}
		tmp1 = ((tmp1 + uint32(2)) + tmp3)
	}
	return uint32(255)
}

func price_alt(prices *[]Price, sibs *[]uint32, first uint32, acc *Acc, over *bool) Ar {
	var total uint32 = uint32(len((*prices)))
	var c uint32 = first
	var k uint32 = uint32(0)
	(*acc).work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).flow = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	for ((k < total) && (c != uint32(4294967295))) {
		var tmp1 Price = (*prices)[c]
		var tmp2 uint32 = (*sibs)[c]
		if (tmp2 != uint32(4294967295)) {
			var tmp3 Poly
			tir_t1 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp1.outs, over)
			tmp3 = tir_t1
			var tmp4 Poly
			tir_t2 := poly_add((*acc).work, tmp3, over)
			tmp4 = tir_t2
			(*acc).work = tmp4
			var tmp5 Poly
			tir_t3 := poly_add((*acc).stack, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
			tmp5 = tir_t3
			(*acc).stack = tmp5
		}
		var tmp6 Poly
		tir_t4 := poly_add((*acc).work, tmp1.work, over)
		tmp6 = tir_t4
		(*acc).work = tmp6
		var tmp7 Poly
		tir_t5 := poly_add((*acc).stack, tmp1.stack, over)
		tmp7 = tir_t5
		(*acc).stack = tmp7
		var tmp8 Poly
		tir_t6 := poly_add((*acc).trail, tmp1.trail, over)
		tmp8 = tir_t6
		(*acc).trail = tmp8
		var tmp9 Poly
		tir_t7 := poly_add((*acc).flow, tmp1.outs, over)
		tmp9 = tir_t7
		(*acc).flow = tmp9
		c = tmp2
		k = (k + uint32(1))
	}
	return ArOk
}

func price_call(re Re, whole Price, cert *Cert, over *bool) {
	var novec uint64 = tir_cmul(tir_cadd(uint64(re.ncap), uint64(1)), uint64(2))
	var setup uint64 = tir_cmul(tir_cadd(uint64(re.nregs), novec), uint64(4))
	var deliver uint64 = tir_cmul(novec, uint64(4))
	var reset uint64 = tir_cmul(uint64(re.nregs), uint64(4))
	var capacity Poly
	var scratch Poly = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	var tmp1 Poly = whole.stack
	capacity = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (!(((((tmp1.c0 == uint64(0)) && (tmp1.c1 == uint64(0))) && (tmp1.c2 == uint64(0))) && (tmp1.c3 == uint64(0))) && (tmp1.c4 == uint64(0)))) {
		var tmp2 Poly
		tir_t1 := poly_mul(tmp1, (Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp2 = tir_t1
		var tmp3 Poly
		tir_t2 := poly_add((Poly{base: uint64(1), c0: uint64(4), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp2, over)
		tmp3 = tir_t2
		capacity = tmp3
	}
	var tmp4 Poly
	tir_t3 := poly_mul(capacity, (Poly{base: uint64(1), c0: uint64(12), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp4 = tir_t3
	var tmp5 Poly
	tir_t4 := poly_add(scratch, tmp4, over)
	tmp5 = tir_t4
	scratch = tmp5
	var tmp6 Poly = whole.trail
	capacity = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (!(((((tmp6.c0 == uint64(0)) && (tmp6.c1 == uint64(0))) && (tmp6.c2 == uint64(0))) && (tmp6.c3 == uint64(0))) && (tmp6.c4 == uint64(0)))) {
		var tmp7 Poly
		tir_t5 := poly_mul(tmp6, (Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp7 = tir_t5
		var tmp8 Poly
		tir_t6 := poly_add((Poly{base: uint64(1), c0: uint64(4), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp7, over)
		tmp8 = tir_t6
		capacity = tmp8
	}
	var tmp9 Poly
	tir_t7 := poly_mul(capacity, (Poly{base: uint64(1), c0: uint64(8), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp9 = tir_t7
	var tmp10 Poly
	tir_t8 := poly_add(scratch, tmp9, over)
	tmp10 = tir_t8
	scratch = tmp10
	var tmp11 Poly
	tir_t9 := poly_mul(whole.trail, (Poly{base: uint64(1), c0: uint64(4), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp11 = tir_t9
	var tmp12 Poly
	tir_t10 := poly_add(whole.work, tmp11, over)
	tmp12 = tir_t10
	var tmp13 Poly
	tir_t11 := poly_add((Poly{base: uint64(1), c0: reset, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp12, over)
	tmp13 = tir_t11
	var tmp14 Poly
	tir_t12 := poly_mul(tmp13, (Poly{base: uint64(1), c0: uint64(0), c1: uint64(1), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp14 = tir_t12
	var tmp15 Poly
	tir_t13 := poly_mul(scratch, (Poly{base: uint64(1), c0: uint64(3), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp15 = tir_t13
	var tmp16 Poly
	tir_t14 := poly_add(tmp14, tmp15, over)
	tmp16 = tir_t14
	var tmp17 Poly
	tir_t15 := poly_add((Poly{base: uint64(1), c0: tir_cadd(setup, deliver), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp16, over)
	tmp17 = tir_t15
	(*cert).cost = tmp17
	(*cert).stack = whole.stack
	(*cert).trail = whole.trail
	var tmp18 Poly
	tir_t16 := poly_mul(scratch, (Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
	tmp18 = tir_t16
	var tmp19 Poly
	tir_t17 := poly_add((Poly{base: uint64(1), c0: tir_cadd(setup, deliver), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp18, over)
	tmp19 = tir_t17
	(*cert).mem = tmp19
}

func price_repeat(code []Inst, reps []Rep, regions []Region, prices *[]Price, sibs *[]uint32, at uint32, first uint32, acc *Acc, over *bool) Ar {
	var here Region = regions[at]
	var lo uint32 = here.lo
	var hi uint32 = here.hi
	if (hi <= lo) {
		return ArShape
	}
	var verdict Ar = ArOk
	var head Inst = code[lo]
	(*acc).work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (head.op == OpSplit) {
		tir_t1 := price_span(code, regions, prices, sibs, (lo + uint32(1)), hi, first, acc, over)
		verdict = tir_t1
		if (verdict != ArOk) {
			return verdict
		}
		var tmp1 Poly
		tir_t2 := poly_add((*acc).work, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp1 = tir_t2
		(*acc).work = tmp1
		var tmp2 Poly
		tir_t3 := poly_add((*acc).stack, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp2 = tir_t3
		(*acc).stack = tmp2
		var tmp3 Poly
		tir_t4 := poly_add((*acc).flow, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp3 = tir_t4
		(*acc).flow = tmp3
		return ArOk
	}
	if (head.op != OpRepZero) {
		return ArShape
	}
	if ((hi - lo) < uint32(4)) {
		return ArShape
	}
	var which uint32 = head.arg
	if (which >= uint32(len(reps))) {
		return ArShape
	}
	var rep Rep = reps[which]
	tir_t5 := price_span(code, regions, prices, sibs, (lo + uint32(3)), (hi - uint32(1)), first, acc, over)
	verdict = tir_t5
	if (verdict != ArOk) {
		return verdict
	}
	var branching Poly = (*acc).flow
	if (!(((((branching.base == uint64(1)) && (branching.c1 == uint64(0))) && (branching.c2 == uint64(0))) && (branching.c3 == uint64(0))) && (branching.c4 == uint64(0)))) {
		return ArAmbiguous
	}
	var ways uint64 = branching.c0
	var bounded bool = (rep.hi != uint32(4294967295))
	var ceiling uint64 = uint64(rep.lo)
	if (bounded && (ceiling < uint64(rep.hi))) {
		ceiling = uint64(rep.hi)
	}
	var rounds Poly = (Poly{base: uint64(1), c0: tir_cadd(ceiling, uint64(1)), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (!bounded) {
		rounds = (Poly{base: uint64(1), c0: tir_cadd(uint64(rep.lo), uint64(1)), c1: uint64(1), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	}
	var flow Poly = rounds
	if (ways > uint64(1)) {
		var tmp4 uint64 = tir_cadd(ceiling, uint64(1))
		if (!bounded) {
			tmp4 = tir_cadd(uint64(rep.lo), uint64(2))
		}
		var tmp5 Bound
		tir_t6 := bound_pow(ways, tmp4)
		tmp5 = tir_t6
		if (!tmp5.ok) {
			return ArOverflow
		}
		flow = (Poly{base: uint64(1), c0: tmp5.value, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
		if (!bounded) {
			flow = (Poly{base: ways, c0: tmp5.value, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
		}
	}
	var body Acc = (*acc)
	var per Poly = (Poly{base: uint64(1), c0: ways, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	var tmp6 Poly
	tir_t7 := poly_add(body.work, per, over)
	tmp6 = tir_t7
	var tmp7 Poly
	tir_t8 := poly_add((Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp6, over)
	tmp7 = tir_t8
	var tmp8 Poly
	tir_t9 := poly_mul(flow, tmp7, over)
	tmp8 = tir_t9
	var tmp9 Poly
	tir_t10 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp8, over)
	tmp9 = tir_t10
	(*acc).work = tmp9
	var tmp10 Poly
	tir_t11 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), body.stack, over)
	tmp10 = tir_t11
	var tmp11 Poly
	tir_t12 := poly_mul(flow, tmp10, over)
	tmp11 = tir_t12
	(*acc).stack = tmp11
	var tmp12 Poly
	tir_t13 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), per, over)
	tmp12 = tir_t13
	var leaves Poly = tmp12
	var tmp13 Poly
	tir_t14 := poly_add(leaves, body.trail, over)
	tmp13 = tir_t14
	var tmp14 Poly
	tir_t15 := poly_mul(flow, tmp13, over)
	tmp14 = tir_t15
	var tmp15 Poly
	tir_t16 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp14, over)
	tmp15 = tir_t16
	(*acc).trail = tmp15
	var tmp16 Poly
	tir_t17 := poly_mul(flow, leaves, over)
	tmp16 = tir_t17
	(*acc).flow = tmp16
	return ArOk
}

func price_span(code []Inst, regions []Region, prices *[]Price, sibs *[]uint32, lo uint32, hi uint32, first uint32, acc *Acc, over *bool) Ar {
	var cursor uint32 = first
	var pc uint32 = lo
	tir_loop1:
	for (pc < hi) {
		var tmp1 uint32 = cursor
		if (tmp1 != uint32(4294967295)) {
			var tmp2 Region = regions[tmp1]
			if (tmp2.lo == pc) {
				if (tmp2.hi <= pc) {
					return ArShape
				}
				var tmp3 Price = (*prices)[tmp1]
				var tmp4 Poly = (*acc).flow
				var tmp5 Poly
				tir_t1 := poly_mul(tmp4, tmp3.work, over)
				tmp5 = tir_t1
				var tmp6 Poly
				tir_t2 := poly_add((*acc).work, tmp5, over)
				tmp6 = tir_t2
				(*acc).work = tmp6
				var tmp7 Poly
				tir_t3 := poly_mul(tmp4, tmp3.stack, over)
				tmp7 = tir_t3
				var tmp8 Poly
				tir_t4 := poly_add((*acc).stack, tmp7, over)
				tmp8 = tir_t4
				(*acc).stack = tmp8
				var tmp9 Poly
				tir_t5 := poly_mul(tmp4, tmp3.trail, over)
				tmp9 = tir_t5
				var tmp10 Poly
				tir_t6 := poly_add((*acc).trail, tmp9, over)
				tmp10 = tir_t6
				(*acc).trail = tmp10
				var tmp11 Poly
				tir_t7 := poly_mul(tmp4, tmp3.outs, over)
				tmp11 = tir_t7
				(*acc).flow = tmp11
				pc = tmp2.hi
				cursor = (*sibs)[tmp1]
				continue tir_loop1
			}
		}
		var tmp12 Poly
		tir_t8 := poly_add((*acc).work, (*acc).flow, over)
		tmp12 = tir_t8
		switch code[pc].op {
		case OpChar:
			(*acc).work = tmp12
		case OpCharCI:
			(*acc).work = tmp12
		case OpClass:
			(*acc).work = tmp12
		case OpAny:
			(*acc).work = tmp12
		case OpAnyNoNL:
			(*acc).work = tmp12
		case OpBsr:
			(*acc).work = tmp12
		case OpCirc:
			(*acc).work = tmp12
		case OpCircM:
			(*acc).work = tmp12
		case OpDoll:
			(*acc).work = tmp12
		case OpDollE:
			(*acc).work = tmp12
		case OpDollM:
			(*acc).work = tmp12
		case OpSod:
			(*acc).work = tmp12
		case OpEod:
			(*acc).work = tmp12
		case OpEodn:
			(*acc).work = tmp12
		case OpWordB:
			(*acc).work = tmp12
		case OpNotWordB:
			(*acc).work = tmp12
		case OpSave:
			(*acc).work = tmp12
			var tmp13 Poly
			tir_t9 := poly_add((*acc).trail, (*acc).flow, over)
			tmp13 = tir_t9
			(*acc).trail = tmp13
		case OpAccept:
			(*acc).work = tmp12
			(*acc).flow = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
		default:
			return ArShape
		}
		pc = (pc + uint32(1))
	}
	return ArOk
}

func push_bt(bt *[]Bt, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64, stacklimit uint32, pcv uint32, posv uint32, mark uint32) bool {
	if (stacklimit <= uint32(len((*bt)))) {
		return false
	}
	var tmp1 bool = false
	tir_t1 := charge_grow(uint32(cap((*bt))), uint32(len((*bt))), uint32(12), uint32(178956970), mem, peak, cost, memlimit, costlimit)
	tmp1 = tir_t1
	if (!tmp1) {
		return false
	}
	tir_push(&(*bt), 178956970, (Bt{pc: pcv, pos: posv, mark: mark}))
	return true
}

func push_frame(w *Work, capno uint32, nopts uint32, at uint32, unsup uint32) {
	if (uint32(len((*w).frames)) > uint32(250)) {
		(*w).err = uint32(119)
		(*w).erroff = (at + uint32(1))
		return
	}
	var tmp1 uint32 = uint32(0)
	var tmp2 uint32 = capno
	tir_t1 := alloc_node(w, NdGroup, tmp2, uint32(0), uint32(0))
	tmp1 = tir_t1
	if ((*w).err != uint32(0)) {
		return
	}
	var tmp3 uint32 = uint32(0)
	tir_t2 := alloc_node(w, NdConcat, uint32(0), uint32(0), uint32(0))
	tmp3 = tir_t2
	if ((*w).err != uint32(0)) {
		return
	}
	add_child(w, tmp1, tmp3)
	var tmp4 uint32 = (uint32(len((*w).frames)) - uint32(1))
	var tmp5 uint32 = (*w).frames[tmp4].cat
	add_child(w, tmp5, tmp1)
	var tmp6 uint32 = (*w).opts
	var tmp7 uint32 = at
	var tmp8 uint32 = unsup
	tir_push(&(*w).frames, 251, (Frame{grp: tmp1, alt: uint32(0), cat: tmp3, qual: uint32(0), opts: tmp6, at: tmp7, unsup: tmp8}))
	(*w).opts = nopts
}

func push_job(w *Work, node uint32, here uint32) {
	if (uint32(len((*w).jobs)) >= uint32(2048)) {
		(*w).err = uint32(1002)
		return
	}
	tir_push(&(*w).jobs, 2048, (Job{node: node, phase: uint32(0), cur: uint32(0), mark: uint32(0), base: uint32(0), here: here, arm: uint32(4294967295)}))
}

func push_patch(w *Work, pc uint32) {
	if (uint32(len((*w).patches)) >= uint32(4096)) {
		(*w).err = uint32(1002)
		return
	}
	tir_push(&(*w).patches, 4096, pc)
}

func quantifier(pat []byte, at *uint32, w *Work) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 uint8 = pat[tmp2]
	var tmp4 uint32 = uint32(0)
	var tmp5 uint32 = uint32(4294967295)
	if (tmp3 == uint8(43)) {
		tmp4 = uint32(1)
	}
	if (tmp3 == uint8(63)) {
		tmp5 = uint32(1)
	}
	if (tmp3 == uint8(123)) {
		var tmp6 Quant
		tir_t1 := read_braces(pat, tmp2, w)
		tmp6 = tir_t1
		if ((*w).err != uint32(0)) {
			return
		}
		if (!tmp6.ok) {
			var tmp7 uint32 = uint32(tmp3)
			add_char(w, tmp7)
			(*at) = (tmp2 + uint32(1))
			return
		}
		tmp4 = tmp6.lo
		tmp5 = tmp6.hi
		tmp2 = (tmp6.end - uint32(1))
	}
	tmp2 = (tmp2 + uint32(1))
	var tmp8 uint32 = tmp2
	skip_gaps(pat, &tmp2, w)
	var tmp9 bool = true
	var tmp10 bool = false
	if (tmp2 < tmp1) {
		var tmp11 uint8 = pat[tmp2]
		if (tmp11 == uint8(63)) {
			tmp9 = false
			tmp2 = (tmp2 + uint32(1))
		}
		if (tmp11 == uint8(43)) {
			tmp10 = true
			tmp2 = (tmp2 + uint32(1))
		}
	}
	if (((*w).opts & uint32(16)) != uint32(0)) {
		tmp9 = (!tmp9)
	}
	apply_quant(w, tmp4, tmp5, tmp9, tmp8)
	if ((*w).err != uint32(0)) {
		return
	}
	if tmp10 {
		(*w).err = uint32(1000)
		(*w).erroff = tmp2
		return
	}
	(*at) = tmp2
}

func re_bound(re Re, kind Bk, mcfg uint32, n uint64) Answer {
	if (mcfg != uint32(0)) {
		return (Answer{status: uint32(3), value: uint64(0)})
	}
	if (n > uint64(2147483647)) {
		return (Answer{status: uint32(3), value: uint64(0)})
	}
	var picked Cert
	var ok bool = false
	tir_t1 := re_pick(re, &picked)
	ok = tir_t1
	if (!ok) {
		return (Answer{status: uint32(4), value: uint64(0)})
	}
	var out Bound
	tir_t2 := cert_bound(picked, kind, n)
	out = tir_t2
	if (!out.ok) {
		return (Answer{status: uint32(4), value: uint64(0)})
	}
	return (Answer{status: uint32(0), value: out.value})
}

func re_class(re Re) Answer {
	var picked Cert
	var ok bool = false
	tir_t1 := re_pick(re, &picked)
	ok = tir_t1
	if (!ok) {
		return (Answer{status: uint32(4), value: uint64(0)})
	}
	var value uint64 = uint64(0)
	var known bool = false
	switch picked.complexity {
	case CcNotProvenLinear:
		known = true
	case CcLinear:
		value = uint64(1)
		known = true
	}
	if (!known) {
		return (Answer{status: uint32(4), value: uint64(0)})
	}
	return (Answer{status: uint32(0), value: value})
}

func re_cost(re Re, mcfg uint32, n uint64) Answer {
	var out Answer
	tir_t1 := re_bound(re, BkCost, mcfg, n)
	out = tir_t1
	return out
}

func re_mem(re Re, mcfg uint32, n uint64) Answer {
	var out Answer
	tir_t1 := re_bound(re, BkMem, mcfg, n)
	out = tir_t1
	return out
}

func re_pick(re Re, picked *Cert) bool {
	if re.pike {
		if (!re.haspikecert) {
			return false
		}
		(*picked) = re.pikecert
		return true
	}
	if (!re.hascert) {
		return false
	}
	(*picked) = re.cert
	return true
}

func re_stack(re Re, mcfg uint32, n uint64) Answer {
	var out Answer
	tir_t1 := re_bound(re, BkStack, mcfg, n)
	out = tir_t1
	return out
}

func read_braces(pat []byte, at uint32, w *Work) Quant {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (at + uint32(1))
	var tmp3 Quant = (Quant{ok: false, lo: uint32(0), hi: uint32(0), end: uint32(0)})
	var tmp4 bool = false
	var tmp5 uint32 = uint32(0)
	var tmp6 uint32 = uint32(4294967295)
	var tmp7 bool = false
	var tmp8 bool = false
	var tmp9 uint32 = uint32(0)
	skip_blanks(pat, &tmp2)
	tir_loop1:
	for (tmp2 < tmp1) {
		tir_t1 := ct(pat[tmp2], uint8(4))
		tmp4 = tir_t1
		if (!tmp4) {
			break tir_loop1
		}
		tmp7 = true
		if (tmp5 <= uint32(65535)) {
			tmp5 = ((tmp5 * uint32(10)) + uint32((pat[tmp2] - uint8(48))))
		}
		tmp2 = (tmp2 + uint32(1))
	}
	tmp9 = tmp2
	var tmp10 uint32 = tmp2
	skip_blanks(pat, &tmp2)
	if ((tmp2 < tmp1) && (pat[tmp2] == uint8(44))) {
		tmp2 = (tmp2 + uint32(1))
		skip_blanks(pat, &tmp2)
		tir_loop2:
		for (tmp2 < tmp1) {
			tir_t2 := ct(pat[tmp2], uint8(4))
			tmp4 = tir_t2
			if (!tmp4) {
				break tir_loop2
			}
			if (!tmp8) {
				tmp6 = uint32(0)
				tmp8 = true
			}
			if (tmp6 <= uint32(65535)) {
				tmp6 = ((tmp6 * uint32(10)) + uint32((pat[tmp2] - uint8(48))))
			}
			tmp2 = (tmp2 + uint32(1))
		}
		tmp9 = tmp2
		skip_blanks(pat, &tmp2)
	} else {
		tmp6 = tmp5
	}
	if (!(tmp7 || tmp8)) {
		return tmp3
	}
	if ((tmp2 >= tmp1) || (pat[tmp2] != uint8(125))) {
		return tmp3
	}
	if (tmp5 > uint32(65535)) {
		(*w).err = uint32(105)
		(*w).erroff = tmp10
		return tmp3
	}
	if (tmp8 && (tmp6 > uint32(65535))) {
		(*w).err = uint32(105)
		(*w).erroff = tmp9
		return tmp3
	}
	if (tmp6 < tmp5) {
		(*w).err = uint32(104)
		(*w).erroff = tmp9
		return tmp3
	}
	return (Quant{ok: true, lo: tmp5, hi: tmp6, end: (tmp2 + uint32(1))})
}

func read_digit_escape(pat []byte, at *uint32, w *Work, incls bool, c uint8) Esc {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 uint8 = c
	var tmp4 Esc = (Esc{kind: EkErr, val: uint32(0)})
	var tmp5 bool = false
	if ((!incls) && (tmp3 != uint8(48))) {
		var tmp6 uint32 = (tmp2 - uint32(1))
		var tmp7 uint32 = uint32(0)
		tir_loop1:
		for (tmp6 < tmp1) {
			tir_t1 := ct(pat[tmp6], uint8(4))
			tmp5 = tir_t1
			if (!tmp5) {
				break tir_loop1
			}
			if (tmp7 <= uint32(65535)) {
				tmp7 = ((tmp7 * uint32(10)) + uint32((pat[tmp6] - uint8(48))))
			}
			tmp6 = (tmp6 + uint32(1))
		}
		if (((tmp7 < uint32(10)) || (tmp3 >= uint8(56))) || (tmp7 <= (*w).ncap)) {
			if (tmp7 > uint32(65535)) {
				(*w).err = uint32(161)
				(*w).erroff = tmp6
				return tmp4
			}
			note_ref(w, tmp7, tmp6, uint32(0))
			if ((*w).err != uint32(0)) {
				return tmp4
			}
			(*at) = tmp6
			return (Esc{kind: EkNop, val: uint32(0)})
		}
	}
	if (tmp3 >= uint8(56)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(tmp3)})
	}
	var tmp8 uint32 = uint32((tmp3 - uint8(48)))
	var tmp9 uint32 = uint32(0)
	var tmp10 bool = false
	tir_loop2:
	for ((tmp9 < uint32(2)) && (tmp2 < tmp1)) {
		tir_t2 := ct(pat[tmp2], uint8(16))
		tmp10 = tir_t2
		if (!tmp10) {
			break tir_loop2
		}
		tmp8 = ((tmp8 * uint32(8)) + uint32((pat[tmp2] - uint8(48))))
		tmp9 = (tmp9 + uint32(1))
		tmp2 = (tmp2 + uint32(1))
	}
	if (tmp8 > uint32(255)) {
		(*w).err = uint32(151)
		(*w).erroff = tmp2
		return tmp4
	}
	(*at) = tmp2
	return (Esc{kind: EkChar, val: tmp8})
}

func read_escape(pat []byte, at *uint32, w *Work, incls bool) Esc {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = ((*at) + uint32(1))
	var tmp3 Esc = (Esc{kind: EkErr, val: uint32(0)})
	if (tmp2 >= tmp1) {
		(*w).err = uint32(101)
		(*w).erroff = tmp2
		return tmp3
	}
	var tmp4 uint8 = pat[tmp2]
	tmp2 = (tmp2 + uint32(1))
	if (tmp4 == uint8(110)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(10)})
	}
	if (tmp4 == uint8(114)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(13)})
	}
	if (tmp4 == uint8(116)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(9)})
	}
	if (tmp4 == uint8(102)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(12)})
	}
	if (tmp4 == uint8(97)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(7)})
	}
	if (tmp4 == uint8(101)) {
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32(27)})
	}
	if (tmp4 == uint8(100)) {
		(*at) = tmp2
		return (Esc{kind: EkSet, val: uint32(0)})
	}
	if (tmp4 == uint8(68)) {
		(*at) = tmp2
		return (Esc{kind: EkNegSet, val: uint32(0)})
	}
	if (tmp4 == uint8(119)) {
		(*at) = tmp2
		return (Esc{kind: EkSet, val: uint32(1)})
	}
	if (tmp4 == uint8(87)) {
		(*at) = tmp2
		return (Esc{kind: EkNegSet, val: uint32(1)})
	}
	if (tmp4 == uint8(115)) {
		(*at) = tmp2
		return (Esc{kind: EkSet, val: uint32(2)})
	}
	if (tmp4 == uint8(83)) {
		(*at) = tmp2
		return (Esc{kind: EkNegSet, val: uint32(2)})
	}
	if (tmp4 == uint8(104)) {
		(*at) = tmp2
		return (Esc{kind: EkSet, val: uint32(3)})
	}
	if (tmp4 == uint8(72)) {
		(*at) = tmp2
		return (Esc{kind: EkNegSet, val: uint32(3)})
	}
	if (tmp4 == uint8(118)) {
		(*at) = tmp2
		return (Esc{kind: EkSet, val: uint32(4)})
	}
	if (tmp4 == uint8(86)) {
		(*at) = tmp2
		return (Esc{kind: EkNegSet, val: uint32(4)})
	}
	if (tmp4 == uint8(98)) {
		(*at) = tmp2
		if incls {
			return (Esc{kind: EkChar, val: uint32(8)})
		}
		return (Esc{kind: EkWordB, val: uint32(0)})
	}
	if (((((((((tmp4 == uint8(66)) || (tmp4 == uint8(65))) || (tmp4 == uint8(90))) || (tmp4 == uint8(122))) || (tmp4 == uint8(82))) || (tmp4 == uint8(71))) || (tmp4 == uint8(75))) || (tmp4 == uint8(88))) || (tmp4 == uint8(67))) {
		if incls {
			(*w).err = uint32(107)
			(*w).erroff = tmp2
			return tmp3
		}
		(*at) = tmp2
		if (tmp4 == uint8(66)) {
			return (Esc{kind: EkNotWordB, val: uint32(0)})
		}
		if (tmp4 == uint8(65)) {
			return (Esc{kind: EkSod, val: uint32(0)})
		}
		if (tmp4 == uint8(90)) {
			return (Esc{kind: EkEodn, val: uint32(0)})
		}
		if (tmp4 == uint8(122)) {
			return (Esc{kind: EkEod, val: uint32(0)})
		}
		if (tmp4 == uint8(82)) {
			return (Esc{kind: EkBsr, val: uint32(0)})
		}
		(*w).err = uint32(1000)
		(*w).erroff = tmp2
		return tmp3
	}
	if (tmp4 == uint8(78)) {
		if incls {
			(*w).err = uint32(171)
			(*w).erroff = tmp2
			return tmp3
		}
		(*w).err = uint32(1000)
		(*w).erroff = tmp2
		return tmp3
	}
	if (((((tmp4 == uint8(70)) || (tmp4 == uint8(76))) || (tmp4 == uint8(108))) || (tmp4 == uint8(85))) || (tmp4 == uint8(117))) {
		(*w).err = uint32(137)
		(*w).erroff = tmp2
		return tmp3
	}
	if ((tmp4 == uint8(107)) || (tmp4 == uint8(103))) {
		if incls {
			(*at) = tmp2
			return (Esc{kind: EkChar, val: uint32(tmp4)})
		}
		var tmp5 Esc
		tir_t1 := read_gk(pat, &tmp2, w, (tmp4 == uint8(103)))
		tmp5 = tir_t1
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		(*at) = tmp2
		return tmp5
	}
	if ((tmp4 == uint8(112)) || (tmp4 == uint8(80))) {
		read_ucp(pat, tmp2, w)
		return tmp3
	}
	if (tmp4 == uint8(99)) {
		if (tmp2 >= tmp1) {
			(*w).err = uint32(102)
			(*w).erroff = tmp2
			return tmp3
		}
		var tmp6 uint8 = pat[tmp2]
		tmp2 = (tmp2 + uint32(1))
		if ((tmp6 >= uint8(97)) && (tmp6 <= uint8(122))) {
			tmp6 = (tmp6 - uint8(32))
		}
		if ((tmp6 < uint8(32)) || (tmp6 > uint8(126))) {
			(*w).err = uint32(168)
			(*w).erroff = tmp2
			return tmp3
		}
		(*at) = tmp2
		return (Esc{kind: EkChar, val: uint32((tmp6 ^ uint8(64)))})
	}
	if (tmp4 == uint8(120)) {
		tir_t2 := read_hex(pat, &tmp2, w)
		tmp3 = tir_t2
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		(*at) = tmp2
		return tmp3
	}
	if (tmp4 == uint8(111)) {
		tir_t3 := read_octal_brace(pat, &tmp2, w)
		tmp3 = tir_t3
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		(*at) = tmp2
		return tmp3
	}
	var tmp7 bool = false
	tir_t4 := ct(tmp4, uint8(4))
	tmp7 = tir_t4
	if tmp7 {
		tir_t5 := read_digit_escape(pat, &tmp2, w, incls, tmp4)
		tmp3 = tir_t5
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		(*at) = tmp2
		return tmp3
	}
	var tmp8 bool = false
	tir_t6 := ct(tmp4, uint8(32))
	tmp8 = tir_t6
	if tmp8 {
		(*w).err = uint32(103)
		(*w).erroff = tmp2
		return tmp3
	}
	(*at) = tmp2
	return (Esc{kind: EkChar, val: uint32(tmp4)})
}

func read_gk(pat []byte, at *uint32, w *Work, isg bool) Esc {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 Esc = (Esc{kind: EkErr, val: uint32(0)})
	var tmp4 Esc = (Esc{kind: EkNop, val: uint32(0)})
	var tmp5 uint8 = uint8(0)
	if (tmp2 < tmp1) {
		tmp5 = pat[tmp2]
	}
	var tmp6 bool = false
	var tmp7 uint32 = uint32(0)
	if (!((tmp5 == uint8(123)) || ((tmp5 == uint8(60)) || (tmp5 == uint8(39))))) {
		if (!isg) {
			(*w).err = uint32(169)
			(*w).erroff = tmp2
			return tmp3
		}
		tir_t1 := ref_number_ahead(pat, tmp2)
		tmp6 = tir_t1
		if (!tmp6) {
			(*w).err = uint32(157)
			(*w).erroff = tmp2
			return tmp3
		}
		tir_t2 := read_ref_number(pat, &tmp2, w, uint32(4294967295))
		tmp7 = tir_t2
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		if (tmp7 == uint32(0)) {
			(*w).err = uint32(115)
			(*w).erroff = tmp2
			return tmp3
		}
		note_ref(w, tmp7, tmp2, uint32(0))
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		(*at) = tmp2
		return tmp4
	}
	var tmp8 uint8 = uint8(125)
	if (tmp5 == uint8(60)) {
		tmp8 = uint8(62)
	}
	if (tmp5 == uint8(39)) {
		tmp8 = uint8(39)
	}
	var tmp9 bool = (tmp5 == uint8(123))
	var tmp10 uint32 = (tmp2 + uint32(1))
	if tmp9 {
		skip_blanks(pat, &tmp10)
	}
	if isg {
		tir_t3 := ref_number_ahead(pat, tmp10)
		tmp6 = tir_t3
	}
	if tmp6 {
		tir_t4 := read_ref_number(pat, &tmp10, w, tmp2)
		tmp7 = tir_t4
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		if tmp9 {
			skip_blanks(pat, &tmp10)
		}
		if ((tmp10 >= tmp1) || (pat[tmp10] != tmp8)) {
			(*w).err = uint32(219)
			(*w).erroff = tmp10
			return tmp3
		}
		tmp10 = (tmp10 + uint32(1))
		if (tmp9 && (tmp7 == uint32(0))) {
			(*w).err = uint32(115)
			(*w).erroff = tmp10
			return tmp3
		}
		note_ref(w, tmp7, tmp10, uint32(0))
		if ((*w).err != uint32(0)) {
			return tmp3
		}
		(*at) = tmp10
		return tmp4
	}
	if (tmp10 >= tmp1) {
		(*w).err = uint32(162)
		(*w).erroff = tmp10
		return tmp3
	}
	var tmp11 bool = false
	tir_t5 := ct(pat[tmp10], uint8(4))
	tmp11 = tir_t5
	if tmp11 {
		(*w).err = uint32(144)
		(*w).erroff = (tmp10 + uint32(1))
		return tmp3
	}
	var tmp12 uint32 = tmp10
	var tmp13 bool = false
	tir_loop1:
	for (tmp10 < tmp1) {
		tir_t6 := ct(pat[tmp10], uint8(1))
		tmp13 = tir_t6
		if (!tmp13) {
			break tir_loop1
		}
		tmp10 = (tmp10 + uint32(1))
	}
	if (tmp10 == tmp12) {
		(*w).err = uint32(162)
		(*w).erroff = tmp12
		return tmp3
	}
	var tmp14 uint32 = (tmp10 - tmp12)
	if (tmp14 > uint32(128)) {
		(*w).err = uint32(148)
		(*w).erroff = tmp10
		return tmp3
	}
	if tmp9 {
		skip_blanks(pat, &tmp10)
	}
	if ((tmp10 >= tmp1) || (pat[tmp10] != tmp8)) {
		(*w).err = uint32(142)
		(*w).erroff = tmp10
		return tmp3
	}
	note_ref(w, uint32(4294967295), tmp12, tmp14)
	if ((*w).err != uint32(0)) {
		return tmp3
	}
	(*at) = (tmp10 + uint32(1))
	return tmp4
}

func read_hex(pat []byte, at *uint32, w *Work) Esc {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 Esc = (Esc{kind: EkErr, val: uint32(0)})
	var tmp4 uint32 = uint32(0)
	var tmp5 uint32 = uint32(0)
	var tmp6 bool = false
	if ((tmp2 < tmp1) && (pat[tmp2] == uint8(123))) {
		tmp2 = (tmp2 + uint32(1))
		skip_blanks(pat, &tmp2)
		tir_loop1:
		for (tmp2 < tmp1) {
			tir_t1 := ct(pat[tmp2], uint8(8))
			tmp6 = tir_t1
			if (!tmp6) {
				break tir_loop1
			}
			if (tmp4 <= uint32(1114111)) {
				var tmp7 uint32 = uint32(0)
				tir_t2 := hex_value(pat[tmp2])
				tmp7 = tir_t2
				tmp4 = ((tmp4 * uint32(16)) + tmp7)
			}
			tmp5 = (tmp5 + uint32(1))
			tmp2 = (tmp2 + uint32(1))
		}
		skip_blanks(pat, &tmp2)
		if ((tmp2 >= tmp1) || (pat[tmp2] != uint8(125))) {
			if ((tmp5 == uint32(0)) && (tmp2 >= tmp1)) {
				(*w).err = uint32(178)
				(*w).erroff = tmp2
				return tmp3
			}
			(*w).err = uint32(167)
			(*w).erroff = (tmp2 + uint32(1))
			return tmp3
		}
		if (tmp5 == uint32(0)) {
			(*w).err = uint32(178)
			(*w).erroff = tmp2
			return tmp3
		}
		if (tmp4 > uint32(255)) {
			(*w).err = uint32(134)
			(*w).erroff = tmp2
			return tmp3
		}
		(*at) = (tmp2 + uint32(1))
		return (Esc{kind: EkChar, val: tmp4})
	}
	tir_loop2:
	for ((tmp5 < uint32(2)) && (tmp2 < tmp1)) {
		tir_t3 := ct(pat[tmp2], uint8(8))
		tmp6 = tir_t3
		if (!tmp6) {
			break tir_loop2
		}
		var tmp8 uint32 = uint32(0)
		tir_t4 := hex_value(pat[tmp2])
		tmp8 = tir_t4
		tmp4 = ((tmp4 * uint32(16)) + tmp8)
		tmp5 = (tmp5 + uint32(1))
		tmp2 = (tmp2 + uint32(1))
	}
	if (tmp5 == uint32(0)) {
		(*w).err = uint32(178)
		(*w).erroff = tmp2
		return tmp3
	}
	(*at) = tmp2
	return (Esc{kind: EkChar, val: tmp4})
}

func read_octal_brace(pat []byte, at *uint32, w *Work) Esc {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 Esc = (Esc{kind: EkErr, val: uint32(0)})
	if ((tmp2 >= tmp1) || (pat[tmp2] != uint8(123))) {
		(*w).err = uint32(155)
		(*w).erroff = tmp2
		return tmp3
	}
	tmp2 = (tmp2 + uint32(1))
	skip_blanks(pat, &tmp2)
	var tmp4 uint32 = uint32(0)
	var tmp5 uint32 = uint32(0)
	var tmp6 bool = false
	tir_loop1:
	for (tmp2 < tmp1) {
		tir_t1 := ct(pat[tmp2], uint8(16))
		tmp6 = tir_t1
		if (!tmp6) {
			break tir_loop1
		}
		if (tmp4 <= uint32(1114111)) {
			tmp4 = ((tmp4 * uint32(8)) + uint32((pat[tmp2] - uint8(48))))
		}
		tmp5 = (tmp5 + uint32(1))
		tmp2 = (tmp2 + uint32(1))
	}
	skip_blanks(pat, &tmp2)
	if ((tmp2 >= tmp1) || (pat[tmp2] != uint8(125))) {
		if ((tmp5 == uint32(0)) && (tmp2 >= tmp1)) {
			(*w).err = uint32(178)
			(*w).erroff = tmp2
			return tmp3
		}
		(*w).err = uint32(164)
		(*w).erroff = (tmp2 + uint32(1))
		return tmp3
	}
	if (tmp5 == uint32(0)) {
		(*w).err = uint32(178)
		(*w).erroff = tmp2
		return tmp3
	}
	if (tmp4 > uint32(255)) {
		(*w).err = uint32(134)
		(*w).erroff = tmp2
		return tmp3
	}
	(*at) = (tmp2 + uint32(1))
	return (Esc{kind: EkChar, val: tmp4})
}

func read_ref_number(pat []byte, at *uint32, w *Work, valerr uint32) uint32 {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 bool = (pat[tmp2] == uint8(43))
	var tmp4 bool = (pat[tmp2] == uint8(45))
	if (tmp3 || tmp4) {
		tmp2 = (tmp2 + uint32(1))
	}
	var tmp5 uint32 = uint32(0)
	var tmp6 bool = false
	tir_loop1:
	for (tmp2 < tmp1) {
		tir_t1 := ct(pat[tmp2], uint8(4))
		tmp6 = tir_t1
		if (!tmp6) {
			break tir_loop1
		}
		if (tmp5 <= uint32(65535)) {
			tmp5 = ((tmp5 * uint32(10)) + uint32((pat[tmp2] - uint8(48))))
		}
		tmp2 = (tmp2 + uint32(1))
	}
	(*at) = tmp2
	var tmp7 uint32 = valerr
	if (tmp7 == uint32(4294967295)) {
		tmp7 = tmp2
	}
	var tmp8 uint32 = uint32(65535)
	if tmp3 {
		tmp8 = (tir_k(uint32(65535)) - (*w).ncap)
	}
	if (tmp5 > tmp8) {
		(*w).err = uint32(161)
		(*w).erroff = tmp7
		return uint32(4294967295)
	}
	if ((tmp3 || tmp4) && (tmp5 == uint32(0))) {
		(*w).err = uint32(126)
		(*w).erroff = tmp7
		return uint32(4294967295)
	}
	if tmp4 {
		if (tmp5 > (*w).ncap) {
			(*w).err = uint32(115)
			(*w).erroff = tmp7
			return uint32(4294967295)
		}
		tmp5 = (((*w).ncap + uint32(1)) - tmp5)
	}
	if tmp3 {
		tmp5 = ((*w).ncap + tmp5)
	}
	return tmp5
}

func read_ucp(pat []byte, at uint32, w *Work) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = at
	if (tmp2 >= tmp1) {
		(*w).err = uint32(146)
		(*w).erroff = tmp2
		return
	}
	var tmp3 uint8 = pat[tmp2]
	tmp2 = (tmp2 + uint32(1))
	if (tmp3 == uint8(123)) {
		var tmp4 bool = false
		var tmp5 uint32 = uint32(0)
		var tmp6 bool = false
		tir_loop1:
		for (tmp2 < tmp1) {
			var tmp7 uint8 = pat[tmp2]
			tmp2 = (tmp2 + uint32(1))
			if (((tmp7 == uint8(95)) || (tmp7 == uint8(45))) || ((tmp7 == uint8(32)) || ((tmp7 >= uint8(9)) && (tmp7 <= uint8(13))))) {
				continue tir_loop1
			}
			if (((tmp5 == uint32(0)) && (!tmp4)) && (tmp7 == uint8(94))) {
				tmp4 = true
				continue tir_loop1
			}
			if (tmp7 == uint8(125)) {
				tmp6 = true
				break tir_loop1
			}
			if ((tmp7 < uint8(38)) || (tmp7 > uint8(122))) {
				(*w).err = uint32(146)
				(*w).erroff = tmp2
				return
			}
			tmp5 = (tmp5 + uint32(1))
			if (tmp5 >= uint32(49)) {
				break tir_loop1
			}
		}
		if (!tmp6) {
			(*w).err = uint32(146)
			(*w).erroff = tmp2
			return
		}
		if (tmp5 == uint32(0)) {
			(*w).err = uint32(147)
			(*w).erroff = tmp2
			return
		}
		(*w).err = uint32(1000)
		(*w).erroff = tmp2
		return
	}
	var tmp8 bool = false
	tir_t1 := ct(tmp3, uint8(32))
	tmp8 = tir_t1
	if (!tmp8) {
		(*w).err = uint32(146)
		(*w).erroff = tmp2
		return
	}
	(*w).err = uint32(1000)
	(*w).erroff = tmp2
}

func ref_number_ahead(pat []byte, at uint32) bool {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = at
	var tmp3 bool = false
	if (tmp2 >= tmp1) {
		return false
	}
	var tmp4 uint8 = pat[tmp2]
	if ((tmp4 == uint8(43)) || (tmp4 == uint8(45))) {
		if (tmp1 <= (tmp2 + uint32(1))) {
			return false
		}
		tir_t1 := ct(pat[(tmp2 + uint32(1))], uint8(4))
		tmp3 = tir_t1
		return tmp3
	}
	tir_t2 := ct(tmp4, uint8(4))
	tmp3 = tir_t2
	return tmp3
}

func region_kids(regions []Region, kids *[]uint32, sibs *[]uint32) {
	var total uint32 = uint32(len(regions))
	var i uint32 = uint32(0)
	for (i < total) {
		tir_push(&(*kids), 8208, uint32(4294967295))
		tir_push(&(*sibs), 8208, uint32(4294967295))
		i = (i + uint32(1))
	}
	i = total
	for (i > uint32(1)) {
		i = (i - uint32(1))
		var tmp1 uint32 = regions[i].parent
		tir_t1 := i
		if tir_t1 >= uint32(len((*sibs))) {
			tir_oob(tir_t1, uint32(len((*sibs))))
		}
		(*sibs)[tir_t1] = (*kids)[tmp1]
		tir_t2 := tmp1
		if tir_t2 >= uint32(len((*kids))) {
			tir_oob(tir_t2, uint32(len((*kids))))
		}
		(*kids)[tir_t2] = i
	}
}

func sat_add(a uint64, b uint64, over *bool) uint64 {
	if (a > tir_csub(uint64(9007199254740991), b)) {
		(*over) = true
		return uint64(9007199254740991)
	}
	return tir_cadd(a, b)
}

func sat_mul(a uint64, b uint64, over *bool) uint64 {
	if ((a == uint64(0)) || (b == uint64(0))) {
		return uint64(0)
	}
	if (a > tir_div_counter(uint64(9007199254740991), b, uint64(0))) {
		(*over) = true
		return uint64(9007199254740991)
	}
	return tir_cmul(a, b)
}

func scan_alt(prices []Price, sibs *[]uint32, first uint32, acc *Acc, over *bool) Cr {
	var total uint32 = uint32(len(prices))
	var c uint32 = first
	var k uint32 = uint32(0)
	(*acc).work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).flow = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	for ((k < total) && (c != uint32(4294967295))) {
		var tmp1 Price = prices[c]
		var tmp2 uint32 = (*sibs)[c]
		if (tmp2 != uint32(4294967295)) {
			var tmp3 Poly
			tir_t1 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp1.outs, over)
			tmp3 = tir_t1
			var tmp4 Poly
			tir_t2 := poly_add((*acc).work, tmp3, over)
			tmp4 = tir_t2
			(*acc).work = tmp4
			var tmp5 Poly
			tir_t3 := poly_add((*acc).stack, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
			tmp5 = tir_t3
			(*acc).stack = tmp5
		}
		var tmp6 Poly
		tir_t4 := poly_add((*acc).work, tmp1.work, over)
		tmp6 = tir_t4
		(*acc).work = tmp6
		var tmp7 Poly
		tir_t5 := poly_add((*acc).stack, tmp1.stack, over)
		tmp7 = tir_t5
		(*acc).stack = tmp7
		var tmp8 Poly
		tir_t6 := poly_add((*acc).trail, tmp1.trail, over)
		tmp8 = tir_t6
		(*acc).trail = tmp8
		var tmp9 Poly
		tir_t7 := poly_add((*acc).flow, tmp1.outs, over)
		tmp9 = tir_t7
		(*acc).flow = tmp9
		c = tmp2
		k = (k + uint32(1))
	}
	return CrOk
}

func scan_first(w *Work) {
	var tmp1 uint32 = uint32(len((*w).code))
	var tmp2 uint32 = uint32(0)
	var tmp3 uint32 = ((tmp1 >> 3) + uint32(1))
	for (tmp2 < tmp3) {
		tir_push(&(*w).seen, 2147483647, uint8(0))
		tmp2 = (tmp2 + uint32(1))
	}
	mark_seen(w, uint32(0))
	var tmp4 uint64 = uint64(65696)
	for ((uint32(len((*w).pending)) > uint32(0)) && (tmp4 > uint64(0))) {
		tmp4 = tir_csub(tmp4, uint64(1))
		var tmp5 uint32 = uint32(0)
		tmp5 = tir_pop(&(*w).pending)
		var tmp6 Inst = (*w).code[tmp5]
		var tmp7 uint32 = tmp6.arg
		switch tmp6.op {
		case OpChar:
			if (tmp7 == uint32(13)) {
				(*w).crfirst = uint32(1)
			}
		case OpCharCI:
			if (tmp7 == uint32(13)) {
				(*w).crfirst = uint32(1)
			}
		case OpClass:
			var tmp8 uint32 = ((tmp7 * uint32(32)) + uint32(1))
			if (((*w).classes[tmp8] & uint8(32)) != uint8(0)) {
				(*w).crfirst = uint32(1)
			}
		case OpSplit:
			mark_seen(w, tmp7)
			mark_seen(w, tmp6.alt)
		case OpJump:
			mark_seen(w, tmp7)
		case OpRepLoop:
			var tmp9 Rep = (*w).reps[tmp7]
			mark_seen(w, tmp9.body)
			if (tmp9.lo == uint32(0)) {
				mark_seen(w, tmp9.after)
			}
		case OpRepNext:
			var tmp10 Rep = (*w).reps[tmp7]
			mark_seen(w, tmp10.head)
			mark_seen(w, tmp10.after)
		case OpAny:
			(*w).crfirst = uint32(1)
		case OpAnyNoNL:
			(*w).crfirst = uint32(1)
		case OpBsr:
			(*w).crfirst = uint32(1)
		case OpAccept:
			(*w).crfirst = uint32(1)
		case OpSave:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpRepZero:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpRepEnter:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpCirc:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpCircM:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpDoll:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpDollE:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpDollM:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpSod:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpEod:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpEodn:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpWordB:
			mark_seen(w, (tmp5 + uint32(1)))
		case OpNotWordB:
			mark_seen(w, (tmp5 + uint32(1)))
		}
	}
	if (tmp4 == uint64(0)) {
		(*w).crfirst = uint32(1)
	}
}

func scan_repeat(code []Inst, reps []Rep, regions []Region, prices []Price, sibs *[]uint32, at uint32, first uint32, acc *Acc, over *bool) Cr {
	var here Region = regions[at]
	var lo uint32 = here.lo
	var hi uint32 = here.hi
	if (hi <= lo) {
		return CrShape
	}
	var verdict Cr = CrOk
	var head Inst = code[lo]
	(*acc).work = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).stack = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).trail = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	(*acc).flow = (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (head.op == OpSplit) {
		tir_t1 := scan_span(code, regions, prices, sibs, (lo + uint32(1)), hi, first, acc, over)
		verdict = tir_t1
		if (verdict != CrOk) {
			return verdict
		}
		var tmp1 Poly
		tir_t2 := poly_add((*acc).work, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp1 = tir_t2
		(*acc).work = tmp1
		var tmp2 Poly
		tir_t3 := poly_add((*acc).stack, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp2 = tir_t3
		(*acc).stack = tmp2
		var tmp3 Poly
		tir_t4 := poly_add((*acc).flow, (Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), over)
		tmp3 = tir_t4
		(*acc).flow = tmp3
		return CrOk
	}
	if (head.op != OpRepZero) {
		return CrShape
	}
	if ((hi - lo) < uint32(4)) {
		return CrShape
	}
	var which uint32 = head.arg
	if (which >= uint32(len(reps))) {
		return CrShape
	}
	var rep Rep = reps[which]
	tir_t5 := scan_span(code, regions, prices, sibs, (lo + uint32(3)), (hi - uint32(1)), first, acc, over)
	verdict = tir_t5
	if (verdict != CrOk) {
		return verdict
	}
	var branching Poly = (*acc).flow
	if (!(((((branching.base == uint64(1)) && (branching.c1 == uint64(0))) && (branching.c2 == uint64(0))) && (branching.c3 == uint64(0))) && (branching.c4 == uint64(0)))) {
		return CrAmbiguous
	}
	var ways uint64 = branching.c0
	var bounded bool = (rep.hi != uint32(4294967295))
	var ceiling uint64 = uint64(rep.lo)
	if (bounded && (ceiling < uint64(rep.hi))) {
		ceiling = uint64(rep.hi)
	}
	var rounds Poly = (Poly{base: uint64(1), c0: tir_cadd(ceiling, uint64(1)), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	if (!bounded) {
		rounds = (Poly{base: uint64(1), c0: tir_cadd(uint64(rep.lo), uint64(1)), c1: uint64(1), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	}
	var flow Poly = rounds
	if (ways > uint64(1)) {
		var tmp4 uint64 = tir_cadd(ceiling, uint64(1))
		if (!bounded) {
			tmp4 = tir_cadd(uint64(rep.lo), uint64(2))
		}
		var tmp5 Bound
		tir_t6 := bound_pow(ways, tmp4)
		tmp5 = tir_t6
		if (!tmp5.ok) {
			(*over) = true
		}
		flow = (Poly{base: uint64(1), c0: tmp5.value, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
		if (!bounded) {
			flow = (Poly{base: ways, c0: tmp5.value, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
		}
	}
	var body Acc = (*acc)
	var per Poly = (Poly{base: uint64(1), c0: ways, c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
	var tmp6 Poly
	tir_t7 := poly_add(body.work, per, over)
	tmp6 = tir_t7
	var tmp7 Poly
	tir_t8 := poly_add((Poly{base: uint64(1), c0: uint64(2), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp6, over)
	tmp7 = tir_t8
	var tmp8 Poly
	tir_t9 := poly_mul(flow, tmp7, over)
	tmp8 = tir_t9
	var tmp9 Poly
	tir_t10 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp8, over)
	tmp9 = tir_t10
	(*acc).work = tmp9
	var tmp10 Poly
	tir_t11 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), body.stack, over)
	tmp10 = tir_t11
	var tmp11 Poly
	tir_t12 := poly_mul(flow, tmp10, over)
	tmp11 = tir_t12
	(*acc).stack = tmp11
	var tmp12 Poly
	tir_t13 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), per, over)
	tmp12 = tir_t13
	var leaves Poly = tmp12
	var tmp13 Poly
	tir_t14 := poly_add(leaves, body.trail, over)
	tmp13 = tir_t14
	var tmp14 Poly
	tir_t15 := poly_mul(flow, tmp13, over)
	tmp14 = tir_t15
	var tmp15 Poly
	tir_t16 := poly_add((Poly{base: uint64(1), c0: uint64(1), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)}), tmp14, over)
	tmp15 = tir_t16
	(*acc).trail = tmp15
	var tmp16 Poly
	tir_t17 := poly_mul(flow, leaves, over)
	tmp16 = tir_t17
	(*acc).flow = tmp16
	return CrOk
}

func scan_span(code []Inst, regions []Region, prices []Price, sibs *[]uint32, lo uint32, hi uint32, first uint32, acc *Acc, over *bool) Cr {
	var cursor uint32 = first
	var pc uint32 = lo
	tir_loop1:
	for (pc < hi) {
		var tmp1 uint32 = cursor
		if (tmp1 != uint32(4294967295)) {
			var tmp2 Region = regions[tmp1]
			if (tmp2.lo == pc) {
				if (tmp2.hi <= pc) {
					return CrShape
				}
				var tmp3 Price = prices[tmp1]
				var tmp4 Poly = (*acc).flow
				var tmp5 Poly
				tir_t1 := poly_mul(tmp4, tmp3.work, over)
				tmp5 = tir_t1
				var tmp6 Poly
				tir_t2 := poly_add((*acc).work, tmp5, over)
				tmp6 = tir_t2
				(*acc).work = tmp6
				var tmp7 Poly
				tir_t3 := poly_mul(tmp4, tmp3.stack, over)
				tmp7 = tir_t3
				var tmp8 Poly
				tir_t4 := poly_add((*acc).stack, tmp7, over)
				tmp8 = tir_t4
				(*acc).stack = tmp8
				var tmp9 Poly
				tir_t5 := poly_mul(tmp4, tmp3.trail, over)
				tmp9 = tir_t5
				var tmp10 Poly
				tir_t6 := poly_add((*acc).trail, tmp9, over)
				tmp10 = tir_t6
				(*acc).trail = tmp10
				var tmp11 Poly
				tir_t7 := poly_mul(tmp4, tmp3.outs, over)
				tmp11 = tir_t7
				(*acc).flow = tmp11
				pc = tmp2.hi
				cursor = (*sibs)[tmp1]
				continue tir_loop1
			}
		}
		var tmp12 Poly
		tir_t8 := poly_add((*acc).work, (*acc).flow, over)
		tmp12 = tir_t8
		switch code[pc].op {
		case OpChar:
			(*acc).work = tmp12
		case OpCharCI:
			(*acc).work = tmp12
		case OpClass:
			(*acc).work = tmp12
		case OpAny:
			(*acc).work = tmp12
		case OpAnyNoNL:
			(*acc).work = tmp12
		case OpBsr:
			(*acc).work = tmp12
		case OpCirc:
			(*acc).work = tmp12
		case OpCircM:
			(*acc).work = tmp12
		case OpDoll:
			(*acc).work = tmp12
		case OpDollE:
			(*acc).work = tmp12
		case OpDollM:
			(*acc).work = tmp12
		case OpSod:
			(*acc).work = tmp12
		case OpEod:
			(*acc).work = tmp12
		case OpEodn:
			(*acc).work = tmp12
		case OpWordB:
			(*acc).work = tmp12
		case OpNotWordB:
			(*acc).work = tmp12
		case OpSave:
			(*acc).work = tmp12
			var tmp13 Poly
			tir_t9 := poly_add((*acc).trail, (*acc).flow, over)
			tmp13 = tir_t9
			(*acc).trail = tmp13
		case OpAccept:
			(*acc).work = tmp12
			(*acc).flow = (Poly{base: uint64(1), c0: uint64(0), c1: uint64(0), c2: uint64(0), c3: uint64(0), c4: uint64(0)})
		default:
			return CrOpcode
		}
		pc = (pc + uint32(1))
	}
	return CrOk
}

func set_add(w *Work, base uint32, c uint32) {
	var tmp1 uint32 = (base + uint32((uint8(c) >> 3)))
	var tmp2 uint8 = BITS[(c & uint32(7))]
	tir_t1 := tmp1
	if tir_t1 >= uint32(len((*w).classes)) {
		tir_oob(tir_t1, uint32(len((*w).classes)))
	}
	(*w).classes[tir_t1] = ((*w).classes[tmp1] | tmp2)
}

func set_range(w *Work, base uint32, lo uint32, hi uint32, fold bool) {
	var tmp1 uint32 = lo
	var tmp2 uint32 = base
	for (tmp1 <= hi) {
		set_add(w, tmp2, tmp1)
		if fold {
			var tmp3 uint32 = uint32(FLIP[tmp1])
			set_add(w, tmp2, tmp3)
		}
		tmp1 = (tmp1 + uint32(1))
	}
}

func set_union(w *Work, base uint32, which uint32, neg bool) {
	var tmp1 uint32 = uint32(0)
	var tmp2 uint32 = (which * uint32(32))
	for (tmp1 < uint32(32)) {
		var tmp3 uint8 = SETS[(tmp2 + tmp1)]
		if neg {
			tmp3 = (^tmp3)
		}
		var tmp4 uint32 = (base + tmp1)
		tir_t1 := tmp4
		if tir_t1 >= uint32(len((*w).classes)) {
			tir_oob(tir_t1, uint32(len((*w).classes)))
		}
		(*w).classes[tir_t1] = ((*w).classes[tmp4] | tmp3)
		tmp1 = (tmp1 + uint32(1))
	}
}

func shape_alt(code []Inst, regions []Region, sibs *[]uint32, at uint32, first uint32) Cr {
	var here Region = regions[at]
	var hi uint32 = here.hi
	var total uint32 = uint32(len(regions))
	var p uint32 = here.lo
	var c uint32 = first
	var k uint32 = uint32(0)
	for ((k < total) && (c != uint32(4294967295))) {
		var tmp1 Region = regions[c]
		if (tmp1.kind != RkBranch) {
			return CrChildren
		}
		var tmp2 uint32 = (*sibs)[c]
		if (tmp2 != uint32(4294967295)) {
			if (p >= hi) {
				return CrShape
			}
			var tmp3 Inst = code[p]
			if (tmp3.op != OpSplit) {
				return CrShape
			}
			if (tmp3.arg != (p + uint32(1))) {
				return CrShape
			}
			if (tmp1.lo != (p + uint32(1))) {
				return CrShape
			}
			var tmp4 uint32 = tmp1.hi
			if (tmp4 >= hi) {
				return CrShape
			}
			var tmp5 Inst = code[tmp4]
			if ((tmp5.op != OpJump) || (tmp5.arg != hi)) {
				return CrShape
			}
			if (tmp3.alt != (tmp4 + uint32(1))) {
				return CrShape
			}
			p = (tmp4 + uint32(1))
		} else {
			if ((tmp1.lo != p) || (tmp1.hi != hi)) {
				return CrShape
			}
		}
		c = tmp2
		k = (k + uint32(1))
	}
	if (c != uint32(4294967295)) {
		return CrChildren
	}
	if (k < uint32(2)) {
		return CrShape
	}
	return CrOk
}

func shape_repeat(code []Inst, reps []Rep, regions []Region, sibs *[]uint32, at uint32, first uint32) Cr {
	var here Region = regions[at]
	var lo uint32 = here.lo
	var hi uint32 = here.hi
	if (hi <= lo) {
		return CrShape
	}
	var head Inst = code[lo]
	var body Cr = CrOk
	if (head.op == OpSplit) {
		var tmp1 bool = ((head.arg == (lo + uint32(1))) && (head.alt == hi))
		var tmp2 bool = ((head.arg == hi) && (head.alt == (lo + uint32(1))))
		if (!(tmp1 || tmp2)) {
			return CrShape
		}
		tir_t1 := shape_span(code, regions, sibs, (lo + uint32(1)), hi, first)
		body = tir_t1
		return body
	}
	if (head.op != OpRepZero) {
		return CrShape
	}
	if ((hi - lo) < uint32(4)) {
		return CrShape
	}
	var which uint32 = head.arg
	if (which >= uint32(len(reps))) {
		return CrShape
	}
	var tmp3 Inst = code[(lo + uint32(1))]
	if ((tmp3.op != OpRepLoop) || (tmp3.arg != which)) {
		return CrShape
	}
	var tmp4 Inst = code[(lo + uint32(2))]
	if ((tmp4.op != OpRepEnter) || (tmp4.arg != which)) {
		return CrShape
	}
	var tail Inst = code[(hi - uint32(1))]
	if ((tail.op != OpRepNext) || (tail.arg != which)) {
		return CrShape
	}
	var rep Rep = reps[which]
	if ((rep.head != (lo + uint32(1))) || ((rep.body != (lo + uint32(2))) || (rep.after != hi))) {
		return CrShape
	}
	tir_t2 := shape_span(code, regions, sibs, (lo + uint32(3)), (hi - uint32(1)), first)
	body = tir_t2
	return body
}

func shape_span(code []Inst, regions []Region, sibs *[]uint32, lo uint32, hi uint32, first uint32) Cr {
	var cursor uint32 = first
	var pc uint32 = lo
	tir_loop1:
	for (pc < hi) {
		var tmp1 uint32 = cursor
		if (tmp1 != uint32(4294967295)) {
			var tmp2 Region = regions[tmp1]
			if (tmp2.lo < pc) {
				return CrShape
			}
			if (tmp2.lo == pc) {
				if ((tmp2.hi <= pc) || (tmp2.hi > hi)) {
					return CrShape
				}
				pc = tmp2.hi
				cursor = (*sibs)[tmp1]
				continue tir_loop1
			}
		}
		switch code[pc].op {
		case OpChar:
			pc = (pc + uint32(1))
		case OpCharCI:
			pc = (pc + uint32(1))
		case OpClass:
			pc = (pc + uint32(1))
		case OpAny:
			pc = (pc + uint32(1))
		case OpAnyNoNL:
			pc = (pc + uint32(1))
		case OpBsr:
			pc = (pc + uint32(1))
		case OpCirc:
			pc = (pc + uint32(1))
		case OpCircM:
			pc = (pc + uint32(1))
		case OpDoll:
			pc = (pc + uint32(1))
		case OpDollE:
			pc = (pc + uint32(1))
		case OpDollM:
			pc = (pc + uint32(1))
		case OpSod:
			pc = (pc + uint32(1))
		case OpEod:
			pc = (pc + uint32(1))
		case OpEodn:
			pc = (pc + uint32(1))
		case OpWordB:
			pc = (pc + uint32(1))
		case OpNotWordB:
			pc = (pc + uint32(1))
		case OpSave:
			pc = (pc + uint32(1))
		case OpAccept:
			pc = (pc + uint32(1))
		default:
			return CrOpcode
		}
	}
	if (cursor != uint32(4294967295)) {
		return CrChildren
	}
	return CrOk
}

func skip_blanks(pat []byte, at *uint32) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	tir_loop1:
	for (tmp2 < tmp1) {
		if ((pat[tmp2] != uint8(32)) && (pat[tmp2] != uint8(9))) {
			break tir_loop1
		}
		tmp2 = (tmp2 + uint32(1))
	}
	(*at) = tmp2
}

func skip_gaps(pat []byte, at *uint32, w *Work) {
	var tmp1 uint32 = uint32(len(pat))
	var tmp2 uint32 = (*at)
	var tmp3 bool = (((*w).opts & uint32(8)) != uint32(0))
	var tmp4 bool = false
	tir_loop1:
	for (tmp2 < tmp1) {
		var tmp5 uint8 = pat[tmp2]
		if tmp3 {
			tir_t1 := ct(tmp5, uint8(2))
			tmp4 = tir_t1
			if tmp4 {
				tmp2 = (tmp2 + uint32(1))
				continue tir_loop1
			}
			if (tmp5 == uint8(35)) {
				var tmp6 uint32 = (tmp2 + uint32(1))
				tir_loop2:
				for (tmp6 < tmp1) {
					var tmp7 uint32 = uint32(0)
					tir_t2 := newline_at(pat, tmp6, (*w).nltype)
					tmp7 = tir_t2
					if (tmp7 != uint32(0)) {
						tmp6 = (tmp6 + tmp7)
						break tir_loop2
					}
					tmp6 = (tmp6 + uint32(1))
				}
				tmp2 = tmp6
				continue tir_loop1
			}
		}
		if (!((tmp5 == uint8(40)) && ((tmp1 > (tmp2 + uint32(2))) && ((pat[(tmp2 + uint32(1))] == uint8(63)) && (pat[(tmp2 + uint32(2))] == uint8(35)))))) {
			break tir_loop1
		}
		var tmp8 uint32 = (tmp2 + uint32(3))
		for ((tmp8 < tmp1) && (pat[tmp8] != uint8(41))) {
			tmp8 = (tmp8 + uint32(1))
		}
		if (tmp8 >= tmp1) {
			break tir_loop1
		}
		tmp2 = (tmp8 + uint32(1))
	}
	(*at) = tmp2
}

func walk_alt(w *Work, top uint32, job Job, nd Node) {
	var tmp1 uint32 = top
	var tmp2 Job
	_ = tmp2
	var tmp3 uint32 = uint32(0)
	if (job.phase == uint32(2)) {
		var tmp4 uint32 = uint32(len((*w).code))
		for (job.base < uint32(len((*w).patches))) {
			var tmp5 uint32 = uint32(0)
			tmp5 = tir_pop(&(*w).patches)
			tir_t1 := tmp5
			if tir_t1 >= uint32(len((*w).code)) {
				tir_oob(tir_t1, uint32(len((*w).code)))
			}
			(*w).code[tir_t1].arg = tmp4
		}
		close_region(w, job.arm)
		close_region(w, job.here)
		tmp2 = tir_pop(&(*w).jobs)
		return
	}
	if (job.phase == uint32(3)) {
		tmp2 = tir_pop(&(*w).jobs)
		return
	}
	var tmp6 uint32 = nd.first
	if (job.phase == uint32(0)) {
		tir_t2 := tmp1
		if tir_t2 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t2, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t2].base = uint32(len((*w).patches))
	} else {
		close_region(w, job.arm)
		tir_t3 := emit(w, OpJump, uint32(0), uint32(0))
		tmp3 = tir_t3
		push_patch(w, tmp3)
		if ((*w).err != uint32(0)) {
			return
		}
		tir_t4 := job.mark
		if tir_t4 >= uint32(len((*w).code)) {
			tir_oob(tir_t4, uint32(len((*w).code)))
		}
		(*w).code[tir_t4].alt = uint32(len((*w).code))
		tmp6 = (*w).nodes[job.cur].nxt
	}
	var tmp7 bool = ((*w).nodes[tmp6].nxt == uint32(0))
	var tmp8 bool = ((job.phase == uint32(0)) && tmp7)
	var tmp9 uint32 = job.here
	if (!tmp8) {
		if (job.phase == uint32(0)) {
			tir_t5 := open_region(w, RkAlt, job.here)
			tmp9 = tir_t5
			tir_t6 := tmp1
			if tir_t6 >= uint32(len((*w).jobs)) {
				tir_oob(tir_t6, uint32(len((*w).jobs)))
			}
			(*w).jobs[tir_t6].here = tmp9
		}
	}
	if tmp7 {
		tir_t7 := tmp1
		if tir_t7 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t7, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t7].phase = uint32(2)
		if tmp8 {
			tir_t8 := tmp1
			if tir_t8 >= uint32(len((*w).jobs)) {
				tir_oob(tir_t8, uint32(len((*w).jobs)))
			}
			(*w).jobs[tir_t8].phase = uint32(3)
		}
	} else {
		tir_t9 := emit(w, OpSplit, uint32(0), uint32(0))
		tmp3 = tir_t9
		if ((*w).err != uint32(0)) {
			return
		}
		tir_t10 := tmp3
		if tir_t10 >= uint32(len((*w).code)) {
			tir_oob(tir_t10, uint32(len((*w).code)))
		}
		(*w).code[tir_t10].arg = (tmp3 + uint32(1))
		tir_t11 := tmp1
		if tir_t11 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t11, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t11].mark = tmp3
		tir_t12 := tmp1
		if tir_t12 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t12, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t12].phase = uint32(1)
	}
	if (!tmp8) {
		var tmp10 uint32 = uint32(0)
		tir_t13 := open_region(w, RkBranch, tmp9)
		tmp10 = tir_t13
		tir_t14 := tmp1
		if tir_t14 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t14, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t14].arm = tmp10
		tmp9 = tmp10
	}
	tir_t15 := tmp1
	if tir_t15 >= uint32(len((*w).jobs)) {
		tir_oob(tir_t15, uint32(len((*w).jobs)))
	}
	(*w).jobs[tir_t15].cur = tmp6
	push_job(w, tmp6, tmp9)
}

func walk_repeat(w *Work, top uint32, job Job, nd Node) {
	var tmp1 uint32 = top
	var tmp2 Job
	_ = tmp2
	var tmp3 uint32 = uint32(0)
	var tmp4 bool = (nd.opts != uint32(0))
	if (job.phase == uint32(1)) {
		var tmp5 uint32 = job.mark
		var tmp6 uint32 = uint32(len((*w).code))
		if tmp4 {
			tir_t1 := tmp5
			if tir_t1 >= uint32(len((*w).code)) {
				tir_oob(tir_t1, uint32(len((*w).code)))
			}
			(*w).code[tir_t1].arg = (tmp5 + uint32(1))
			tir_t2 := tmp5
			if tir_t2 >= uint32(len((*w).code)) {
				tir_oob(tir_t2, uint32(len((*w).code)))
			}
			(*w).code[tir_t2].alt = tmp6
		} else {
			tir_t3 := tmp5
			if tir_t3 >= uint32(len((*w).code)) {
				tir_oob(tir_t3, uint32(len((*w).code)))
			}
			(*w).code[tir_t3].arg = tmp6
			tir_t4 := tmp5
			if tir_t4 >= uint32(len((*w).code)) {
				tir_oob(tir_t4, uint32(len((*w).code)))
			}
			(*w).code[tir_t4].alt = (tmp5 + uint32(1))
		}
		close_region(w, job.here)
		tmp2 = tir_pop(&(*w).jobs)
		return
	}
	if (job.phase == uint32(2)) {
		var tmp7 uint32 = job.mark
		tir_t5 := emit(w, OpRepNext, tmp7, uint32(0))
		tmp3 = tir_t5
		if ((*w).err != uint32(0)) {
			return
		}
		tir_t6 := tmp7
		if tir_t6 >= uint32(len((*w).reps)) {
			tir_oob(tir_t6, uint32(len((*w).reps)))
		}
		(*w).reps[tir_t6].after = uint32(len((*w).code))
		close_region(w, job.here)
		tmp2 = tir_pop(&(*w).jobs)
		return
	}
	if (job.phase == uint32(3)) {
		tmp2 = tir_pop(&(*w).jobs)
		return
	}
	var tmp8 uint32 = nd.val
	var tmp9 uint32 = nd.aux
	var tmp10 uint32 = nd.first
	if (tmp9 == uint32(0)) {
		tmp2 = tir_pop(&(*w).jobs)
		return
	}
	if ((tmp8 == uint32(1)) && (tmp9 == uint32(1))) {
		tir_t7 := tmp1
		if tir_t7 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t7, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t7].phase = uint32(3)
		push_job(w, tmp10, job.here)
		return
	}
	var tmp11 uint32 = uint32(0)
	tir_t8 := open_region(w, RkRepeat, job.here)
	tmp11 = tir_t8
	tir_t9 := tmp1
	if tir_t9 >= uint32(len((*w).jobs)) {
		tir_oob(tir_t9, uint32(len((*w).jobs)))
	}
	(*w).jobs[tir_t9].here = tmp11
	if ((tmp8 == uint32(0)) && (tmp9 == uint32(1))) {
		tir_t10 := emit(w, OpSplit, uint32(0), uint32(0))
		tmp3 = tir_t10
		if ((*w).err != uint32(0)) {
			return
		}
		tir_t11 := tmp1
		if tir_t11 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t11, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t11].mark = tmp3
		tir_t12 := tmp1
		if tir_t12 >= uint32(len((*w).jobs)) {
			tir_oob(tir_t12, uint32(len((*w).jobs)))
		}
		(*w).jobs[tir_t12].phase = uint32(1)
		push_job(w, tmp10, tmp11)
		return
	}
	var tmp12 uint32 = uint32(0)
	tir_t13 := new_rep(w)
	tmp12 = tir_t13
	if ((*w).err != uint32(0)) {
		return
	}
	tir_t14 := emit(w, OpRepZero, tmp12, uint32(0))
	tmp3 = tir_t14
	var tmp13 uint32 = uint32(0)
	tir_t15 := emit(w, OpRepLoop, tmp12, uint32(0))
	tmp13 = tir_t15
	tir_t16 := emit(w, OpRepEnter, tmp12, uint32(0))
	tmp3 = tir_t16
	if ((*w).err != uint32(0)) {
		return
	}
	tir_t17 := tmp12
	if tir_t17 >= uint32(len((*w).reps)) {
		tir_oob(tir_t17, uint32(len((*w).reps)))
	}
	(*w).reps[tir_t17].lo = tmp8
	tir_t18 := tmp12
	if tir_t18 >= uint32(len((*w).reps)) {
		tir_oob(tir_t18, uint32(len((*w).reps)))
	}
	(*w).reps[tir_t18].hi = tmp9
	tir_t19 := tmp12
	if tir_t19 >= uint32(len((*w).reps)) {
		tir_oob(tir_t19, uint32(len((*w).reps)))
	}
	(*w).reps[tir_t19].greedy = tmp4
	tir_t20 := tmp12
	if tir_t20 >= uint32(len((*w).reps)) {
		tir_oob(tir_t20, uint32(len((*w).reps)))
	}
	(*w).reps[tir_t20].head = tmp13
	tir_t21 := tmp12
	if tir_t21 >= uint32(len((*w).reps)) {
		tir_oob(tir_t21, uint32(len((*w).reps)))
	}
	(*w).reps[tir_t21].body = (tmp13 + uint32(1))
	tir_t22 := tmp1
	if tir_t22 >= uint32(len((*w).jobs)) {
		tir_oob(tir_t22, uint32(len((*w).jobs)))
	}
	(*w).jobs[tir_t22].mark = tmp12
	tir_t23 := tmp1
	if tir_t23 >= uint32(len((*w).jobs)) {
		tir_oob(tir_t23, uint32(len((*w).jobs)))
	}
	(*w).jobs[tir_t23].phase = uint32(2)
	push_job(w, tmp10, tmp11)
}

func word_edge(subj []byte, pos uint32) bool {
	var tmp1 uint32 = uint32(len(subj))
	var tmp2 bool = false
	var tmp3 bool = false
	if (pos > uint32(0)) {
		tir_t1 := ct(subj[(pos - uint32(1))], uint8(1))
		tmp2 = tir_t1
	}
	if (pos < tmp1) {
		tir_t2 := ct(subj[pos], uint8(1))
		tmp3 = tir_t2
	}
	return (tmp2 != tmp3)
}

func write_reg(regs *[]uint32, trail *[]Undo, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64, btlen uint32, slot uint32, value uint32) bool {
	if (btlen > uint32(0)) {
		var tmp1 bool = false
		tir_t1 := charge_grow(uint32(cap((*trail))), uint32(len((*trail))), uint32(8), uint32(268435455), mem, peak, cost, memlimit, costlimit)
		tmp1 = tir_t1
		if (!tmp1) {
			return false
		}
		tir_push(&(*trail), 268435455, (Undo{slot: slot, old: (*regs)[slot]}))
	}
	tir_t2 := slot
	if tir_t2 >= uint32(len((*regs))) {
		tir_oob(tir_t2, uint32(len((*regs))))
	}
	(*regs)[tir_t2] = value
	return true
}

// The exported façade. Go cannot reach a lower-case name from another
// package and TIR names are printed verbatim, so the wrapper next door
// talks to the program through these. They add no behaviour of their own.

func Tir_add_char(w *Work, c uint32) {
	add_char(w, c)
}

func Tir_add_child(w *Work, parent uint32, child uint32) {
	add_child(w, parent, child)
}

func Tir_alloc_node(w *Work, kind Nd, val uint32, aux uint32, nopts uint32) uint32 {
	return alloc_node(w, kind, val, aux, nopts)
}

func Tir_apply_quant(w *Work, lo uint32, hi uint32, greedy bool, erroff uint32) {
	apply_quant(w, lo, hi, greedy, erroff)
}

func Tir_at_line_end(subj []byte, pos uint32, nltype uint32) bool {
	return at_line_end(subj, pos, nltype)
}

func Tir_attach_atom(w *Work, kind Nd, val uint32, aux uint32) {
	attach_atom(w, kind, val, aux)
}

func Tir_attach_escape(w *Work, esc Esc) {
	attach_escape(w, esc)
}

func Tir_bound_add(a Bound, b Bound) Bound {
	return bound_add(a, b)
}

func Tir_bound_mul(a Bound, b Bound) Bound {
	return bound_mul(a, b)
}

func Tir_bound_pow(base uint64, exp uint64) Bound {
	return bound_pow(base, exp)
}

func Tir_bsr_at(subj []byte, pos uint32, bsr uint32) uint32 {
	return bsr_at(subj, pos, bsr)
}

func Tir_bt_match(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ov *[]uint32, use *Usage) uint32 {
	return bt_match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use)
}

func Tir_bt_run(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, regs *[]uint32, bt *[]Bt, trail *[]Undo, ov *[]uint32, use *Usage) uint32 {
	return bt_run(re, subj, start, mopts, costlimit, stacklimit, memlimit, regs, bt, trail, ov, use)
}

func Tir_cert_bound(cert Cert, kind Bk, n uint64) Bound {
	return cert_bound(cert, kind, n)
}

func Tir_cert_build(re Re, cert *Cert) Ar {
	return cert_build(re, cert)
}

func Tir_cert_check(re Re, config Cfg, cert Cert) Cr {
	return cert_check(re, config, cert)
}

func Tir_cert_install(re Re, cert *Cert, has *bool, pcert *Cert, haspike *bool) Cr {
	return cert_install(re, cert, has, pcert, haspike)
}

func Tir_cert_shape(re Re) Cr {
	return cert_shape(re)
}

func Tir_charge_call(re Re, cert Cert, whole Price, over *bool) Cr {
	return charge_call(re, cert, whole, over)
}

func Tir_charge_grow(oldcap uint32, lenv uint32, esize uint32, maxv uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	return charge_grow(oldcap, lenv, esize, maxv, mem, peak, cost, memlimit, costlimit)
}

func Tir_check_possess(w *Work) {
	check_possess(w)
}

func Tir_class_after_set(w *Work, at uint32, pat []byte) {
	class_after_set(w, at, pat)
}

func Tir_class_element(w *Work, at *uint32, quoting *bool, pat []byte, base uint32, lo uint32, fold bool) {
	class_element(w, at, quoting, pat, base, lo, fold)
}

func Tir_class_from_set(w *Work, which uint32, neg bool) {
	class_from_set(w, which, neg)
}

func Tir_class_has(classes []byte, idx uint32, c uint8) bool {
	return class_has(classes, idx, c)
}

func Tir_class_skip(pat []byte, at *uint32, quoting *bool) {
	class_skip(pat, at, quoting)
}

func Tir_close_group(w *Work) {
	close_group(w)
}

func Tir_close_region(w *Work, at uint32) {
	close_region(w, at)
}

func Tir_compile(pat []byte, popts uint32, nltype uint32, bsr uint32, out *Out) {
	compile(pat, popts, nltype, bsr, out)
}

func Tir_ct(c uint8, bit uint8) bool {
	return ct(c, bit)
}

func Tir_ctx_create(re Re, mcfg uint32, maxlen uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ctx *Ctx) uint32 {
	return ctx_create(re, mcfg, maxlen, costlimit, stacklimit, memlimit, ctx)
}

func Tir_ctx_match(ctx *Ctx, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, ov *[]uint32, use *Usage) uint32 {
	return ctx_match(ctx, subj, start, mopts, costlimit, stacklimit, ov, use)
}

func Tir_drop_empty_region(w *Work, at uint32) {
	drop_empty_region(w, at)
}

func Tir_emit(w *Work, op Op, arg uint32, alt uint32) uint32 {
	return emit(w, op, arg, alt)
}

func Tir_generate(w *Work, endanchored bool) {
	generate(w, endanchored)
}

func Tir_hex_value(c uint8) uint32 {
	return hex_value(c)
}

func Tir_identity_of(kind Nd, aux uint32) uint32 {
	return identity_of(kind, aux)
}

func Tir_mark_seen(w *Work, pc uint32) {
	mark_seen(w, pc)
}

func Tir_match(re Re, subj []byte, start uint32, mopts uint32, mcfg uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ov *[]uint32, use *Usage) uint32 {
	return match(re, subj, start, mopts, mcfg, costlimit, stacklimit, memlimit, ov, use)
}

func Tir_name_taken(pat []byte, off uint32, nlen uint32, w *Work) bool {
	return name_taken(pat, off, nlen, w)
}

func Tir_named_group(pat []byte, at *uint32, w *Work, start uint32, term uint8, here uint32) {
	named_group(pat, at, w, start, term, here)
}

func Tir_new_branch(w *Work) {
	new_branch(w)
}

func Tir_new_class(w *Work) uint32 {
	return new_class(w)
}

func Tir_new_rep(w *Work) uint32 {
	return new_rep(w)
}

func Tir_newline_at(subj []byte, pos uint32, nltype uint32) uint32 {
	return newline_at(subj, pos, nltype)
}

func Tir_newline_before(subj []byte, pos uint32, nltype uint32) uint32 {
	return newline_before(subj, pos, nltype)
}

func Tir_note_element(w *Work, lo uint32, hi uint32, ranged bool) {
	note_element(w, lo, hi, ranged)
}

func Tir_note_ref(w *Work, num uint32, off uint32, nlen uint32) {
	note_ref(w, num, off, nlen)
}

func Tir_open_group(pat []byte, at *uint32, w *Work) {
	open_group(pat, at, w)
}

func Tir_open_region(w *Work, kind Rk, parent uint32) uint32 {
	return open_region(w, kind, parent)
}

func Tir_parse(pat []byte, popts uint32, nltype uint32, w *Work) {
	parse(pat, popts, nltype, w)
}

func Tir_parse_class(pat []byte, at *uint32, w *Work) uint32 {
	return parse_class(pat, at, w)
}

func Tir_pike_add(list *[]Th, stk *[]Th, seen *[]byte, pool *[]uint32, rc *[]uint32, free *[]uint32, code []Inst, reps []Rep, subj []byte, pos uint32, novec uint32, nltype uint32, notbol bool, noteol bool, pc0 uint32, h0 uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	return pike_add(list, stk, seen, pool, rc, free, code, reps, subj, pos, novec, nltype, notbol, noteol, pc0, h0, mem, peak, cost, memlimit, costlimit)
}

func Tir_pike_check(re Re, cert Cert) Cr {
	return pike_check(re, cert)
}

func Tir_pike_defer(held *[]Th, pcv uint32, hv uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	return pike_defer(held, pcv, hv, mem, peak, cost, memlimit, costlimit)
}

func Tir_pike_drop(rc *[]uint32, free *[]uint32, h uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	return pike_drop(rc, free, h, mem, peak, cost, memlimit, costlimit)
}

func Tir_pike_hollow(re Re, which uint32) bool {
	return pike_hollow(re, which)
}

func Tir_pike_match(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, ov *[]uint32, use *Usage) uint32 {
	return pike_match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use)
}

func Tir_pike_ok(re Re) bool {
	return pike_ok(re)
}

func Tir_pike_park(held *[]Th, pcv uint32, hv uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	return pike_park(held, pcv, hv, mem, peak, cost, memlimit, costlimit)
}

func Tir_pike_price(re Re, cert *Cert) bool {
	return pike_price(re, cert)
}

func Tir_pike_room(re Re, room *Room, over *bool) {
	pike_room(re, room, over)
}

func Tir_pike_run(re Re, subj []byte, start uint32, mopts uint32, costlimit uint64, stacklimit uint32, memlimit uint64, clist *[]Th, nlist *[]Th, stk *[]Th, seen *[]byte, pool *[]uint32, rc *[]uint32, free *[]uint32, ov *[]uint32, use *Usage) uint32 {
	return pike_run(re, subj, start, mopts, costlimit, stacklimit, memlimit, clist, nlist, stk, seen, pool, rc, free, ov, use)
}

func Tir_pike_take(pool *[]uint32, rc *[]uint32, free *[]uint32, novec uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) uint32 {
	return pike_take(pool, rc, free, novec, mem, peak, cost, memlimit, costlimit)
}

func Tir_pike_write(pool *[]uint32, rc *[]uint32, free *[]uint32, novec uint32, h *uint32, slot uint32, value uint32, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64) bool {
	return pike_write(pool, rc, free, novec, h, slot, value, mem, peak, cost, memlimit, costlimit)
}

func Tir_poly_add(a Poly, b Poly, over *bool) Poly {
	return poly_add(a, b, over)
}

func Tir_poly_eq(a Poly, b Poly) bool {
	return poly_eq(a, b)
}

func Tir_poly_ge(a Poly, b Poly) bool {
	return poly_ge(a, b)
}

func Tir_poly_mul(a Poly, b Poly, over *bool) Poly {
	return poly_mul(a, b, over)
}

func Tir_poly_norm(p Poly) Poly {
	return poly_norm(p)
}

func Tir_poly_value(p Poly, n uint64) Bound {
	return poly_value(p, n)
}

func Tir_posix_end(pat []byte, at uint32) uint32 {
	return posix_end(pat, at)
}

func Tir_posix_item(w *Work, pat []byte, at uint32, stop uint32, base uint32, fold bool) {
	posix_item(w, pat, at, stop, base, fold)
}

func Tir_posix_set(pat []byte, off uint32, nlen uint32) uint32 {
	return posix_set(pat, off, nlen)
}

func Tir_price_alt(prices *[]Price, sibs *[]uint32, first uint32, acc *Acc, over *bool) Ar {
	return price_alt(prices, sibs, first, acc, over)
}

func Tir_price_call(re Re, whole Price, cert *Cert, over *bool) {
	price_call(re, whole, cert, over)
}

func Tir_price_repeat(code []Inst, reps []Rep, regions []Region, prices *[]Price, sibs *[]uint32, at uint32, first uint32, acc *Acc, over *bool) Ar {
	return price_repeat(code, reps, regions, prices, sibs, at, first, acc, over)
}

func Tir_price_span(code []Inst, regions []Region, prices *[]Price, sibs *[]uint32, lo uint32, hi uint32, first uint32, acc *Acc, over *bool) Ar {
	return price_span(code, regions, prices, sibs, lo, hi, first, acc, over)
}

func Tir_push_bt(bt *[]Bt, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64, stacklimit uint32, pcv uint32, posv uint32, mark uint32) bool {
	return push_bt(bt, mem, peak, cost, memlimit, costlimit, stacklimit, pcv, posv, mark)
}

func Tir_push_frame(w *Work, capno uint32, nopts uint32, at uint32, unsup uint32) {
	push_frame(w, capno, nopts, at, unsup)
}

func Tir_push_job(w *Work, node uint32, here uint32) {
	push_job(w, node, here)
}

func Tir_push_patch(w *Work, pc uint32) {
	push_patch(w, pc)
}

func Tir_quantifier(pat []byte, at *uint32, w *Work) {
	quantifier(pat, at, w)
}

func Tir_re_bound(re Re, kind Bk, mcfg uint32, n uint64) Answer {
	return re_bound(re, kind, mcfg, n)
}

func Tir_re_class(re Re) Answer {
	return re_class(re)
}

func Tir_re_cost(re Re, mcfg uint32, n uint64) Answer {
	return re_cost(re, mcfg, n)
}

func Tir_re_mem(re Re, mcfg uint32, n uint64) Answer {
	return re_mem(re, mcfg, n)
}

func Tir_re_pick(re Re, picked *Cert) bool {
	return re_pick(re, picked)
}

func Tir_re_stack(re Re, mcfg uint32, n uint64) Answer {
	return re_stack(re, mcfg, n)
}

func Tir_read_braces(pat []byte, at uint32, w *Work) Quant {
	return read_braces(pat, at, w)
}

func Tir_read_digit_escape(pat []byte, at *uint32, w *Work, incls bool, c uint8) Esc {
	return read_digit_escape(pat, at, w, incls, c)
}

func Tir_read_escape(pat []byte, at *uint32, w *Work, incls bool) Esc {
	return read_escape(pat, at, w, incls)
}

func Tir_read_gk(pat []byte, at *uint32, w *Work, isg bool) Esc {
	return read_gk(pat, at, w, isg)
}

func Tir_read_hex(pat []byte, at *uint32, w *Work) Esc {
	return read_hex(pat, at, w)
}

func Tir_read_octal_brace(pat []byte, at *uint32, w *Work) Esc {
	return read_octal_brace(pat, at, w)
}

func Tir_read_ref_number(pat []byte, at *uint32, w *Work, valerr uint32) uint32 {
	return read_ref_number(pat, at, w, valerr)
}

func Tir_read_ucp(pat []byte, at uint32, w *Work) {
	read_ucp(pat, at, w)
}

func Tir_ref_number_ahead(pat []byte, at uint32) bool {
	return ref_number_ahead(pat, at)
}

func Tir_region_kids(regions []Region, kids *[]uint32, sibs *[]uint32) {
	region_kids(regions, kids, sibs)
}

func Tir_sat_add(a uint64, b uint64, over *bool) uint64 {
	return sat_add(a, b, over)
}

func Tir_sat_mul(a uint64, b uint64, over *bool) uint64 {
	return sat_mul(a, b, over)
}

func Tir_scan_alt(prices []Price, sibs *[]uint32, first uint32, acc *Acc, over *bool) Cr {
	return scan_alt(prices, sibs, first, acc, over)
}

func Tir_scan_first(w *Work) {
	scan_first(w)
}

func Tir_scan_repeat(code []Inst, reps []Rep, regions []Region, prices []Price, sibs *[]uint32, at uint32, first uint32, acc *Acc, over *bool) Cr {
	return scan_repeat(code, reps, regions, prices, sibs, at, first, acc, over)
}

func Tir_scan_span(code []Inst, regions []Region, prices []Price, sibs *[]uint32, lo uint32, hi uint32, first uint32, acc *Acc, over *bool) Cr {
	return scan_span(code, regions, prices, sibs, lo, hi, first, acc, over)
}

func Tir_set_add(w *Work, base uint32, c uint32) {
	set_add(w, base, c)
}

func Tir_set_range(w *Work, base uint32, lo uint32, hi uint32, fold bool) {
	set_range(w, base, lo, hi, fold)
}

func Tir_set_union(w *Work, base uint32, which uint32, neg bool) {
	set_union(w, base, which, neg)
}

func Tir_shape_alt(code []Inst, regions []Region, sibs *[]uint32, at uint32, first uint32) Cr {
	return shape_alt(code, regions, sibs, at, first)
}

func Tir_shape_repeat(code []Inst, reps []Rep, regions []Region, sibs *[]uint32, at uint32, first uint32) Cr {
	return shape_repeat(code, reps, regions, sibs, at, first)
}

func Tir_shape_span(code []Inst, regions []Region, sibs *[]uint32, lo uint32, hi uint32, first uint32) Cr {
	return shape_span(code, regions, sibs, lo, hi, first)
}

func Tir_skip_blanks(pat []byte, at *uint32) {
	skip_blanks(pat, at)
}

func Tir_skip_gaps(pat []byte, at *uint32, w *Work) {
	skip_gaps(pat, at, w)
}

func Tir_walk_alt(w *Work, top uint32, job Job, nd Node) {
	walk_alt(w, top, job, nd)
}

func Tir_walk_repeat(w *Work, top uint32, job Job, nd Node) {
	walk_repeat(w, top, job, nd)
}

func Tir_word_edge(subj []byte, pos uint32) bool {
	return word_edge(subj, pos)
}

func Tir_write_reg(regs *[]uint32, trail *[]Undo, mem *uint64, peak *uint64, cost *uint64, memlimit uint64, costlimit uint64, btlen uint32, slot uint32, value uint32) bool {
	return write_reg(regs, trail, mem, peak, cost, memlimit, costlimit, btlen, slot, value)
}

func (v *Acc) Tir_work() Poly { return v.work }
func (v *Acc) Tir_stack() Poly { return v.stack }
func (v *Acc) Tir_trail() Poly { return v.trail }
func (v *Acc) Tir_flow() Poly { return v.flow }

func (v *Answer) Tir_status() uint32 { return v.status }
func (v *Answer) Tir_value() uint64 { return v.value }

func (v *Bound) Tir_ok() bool { return v.ok }
func (v *Bound) Tir_value() uint64 { return v.value }

func (v *Bt) Tir_pc() uint32 { return v.pc }
func (v *Bt) Tir_pos() uint32 { return v.pos }
func (v *Bt) Tir_mark() uint32 { return v.mark }

func (v *Cert) Tir_config() Cfg { return v.config }
func (v *Cert) Tir_complexity() Cc { return v.complexity }
func (v *Cert) Tir_cost() Poly { return v.cost }
func (v *Cert) Tir_stack() Poly { return v.stack }
func (v *Cert) Tir_trail() Poly { return v.trail }
func (v *Cert) Tir_mem() Poly { return v.mem }
func (v *Cert) Tir_prices() []Price { return v.prices }

func (v *Ctx) Tir_re() Re { return v.re }
func (v *Ctx) Tir_ready() bool { return v.ready }
func (v *Ctx) Tir_maxlen() uint32 { return v.maxlen }
func (v *Ctx) Tir_costcap() uint64 { return v.costcap }
func (v *Ctx) Tir_stackcap() uint32 { return v.stackcap }
func (v *Ctx) Tir_memcap() uint64 { return v.memcap }

func (v *Esc) Tir_kind() Ek { return v.kind }
func (v *Esc) Tir_val() uint32 { return v.val }

func (v *Frame) Tir_grp() uint32 { return v.grp }
func (v *Frame) Tir_alt() uint32 { return v.alt }
func (v *Frame) Tir_cat() uint32 { return v.cat }
func (v *Frame) Tir_qual() uint32 { return v.qual }
func (v *Frame) Tir_opts() uint32 { return v.opts }
func (v *Frame) Tir_at() uint32 { return v.at }
func (v *Frame) Tir_unsup() uint32 { return v.unsup }

func (v *Inst) Tir_op() Op { return v.op }
func (v *Inst) Tir_arg() uint32 { return v.arg }
func (v *Inst) Tir_alt() uint32 { return v.alt }

func (v *Job) Tir_node() uint32 { return v.node }
func (v *Job) Tir_phase() uint32 { return v.phase }
func (v *Job) Tir_cur() uint32 { return v.cur }
func (v *Job) Tir_mark() uint32 { return v.mark }
func (v *Job) Tir_base() uint32 { return v.base }
func (v *Job) Tir_here() uint32 { return v.here }
func (v *Job) Tir_arm() uint32 { return v.arm }

func (v *NameEnt) Tir_off() uint32 { return v.off }
func (v *NameEnt) Tir_nlen() uint32 { return v.nlen }
func (v *NameEnt) Tir_grp() uint32 { return v.grp }

func (v *Node) Tir_kind() Nd { return v.kind }
func (v *Node) Tir_val() uint32 { return v.val }
func (v *Node) Tir_aux() uint32 { return v.aux }
func (v *Node) Tir_opts() uint32 { return v.opts }
func (v *Node) Tir_first() uint32 { return v.first }
func (v *Node) Tir_last() uint32 { return v.last }
func (v *Node) Tir_nxt() uint32 { return v.nxt }

func (v *Out) Tir_err() uint32 { return v.err }
func (v *Out) Tir_erroff() uint32 { return v.erroff }
func (v *Out) Tir_re() Re { return v.re }

func (v *Poly) Tir_base() uint64 { return v.base }
func (v *Poly) Tir_c0() uint64 { return v.c0 }
func (v *Poly) Tir_c1() uint64 { return v.c1 }
func (v *Poly) Tir_c2() uint64 { return v.c2 }
func (v *Poly) Tir_c3() uint64 { return v.c3 }
func (v *Poly) Tir_c4() uint64 { return v.c4 }

func (v *Price) Tir_work() Poly { return v.work }
func (v *Price) Tir_outs() Poly { return v.outs }
func (v *Price) Tir_stack() Poly { return v.stack }
func (v *Price) Tir_trail() Poly { return v.trail }

func (v *Quant) Tir_ok() bool { return v.ok }
func (v *Quant) Tir_lo() uint32 { return v.lo }
func (v *Quant) Tir_hi() uint32 { return v.hi }
func (v *Quant) Tir_end() uint32 { return v.end }

func (v *Re) Tir_code() []Inst { return v.code }
func (v *Re) Tir_classes() []byte { return v.classes }
func (v *Re) Tir_reps() []Rep { return v.reps }
func (v *Re) Tir_regions() []Region { return v.regions }
func (v *Re) Tir_names() []byte { return v.names }
func (v *Re) Tir_nameents() []NameEnt { return v.nameents }
func (v *Re) Tir_ncap() uint32 { return v.ncap }
func (v *Re) Tir_nname() uint32 { return v.nname }
func (v *Re) Tir_nregs() uint32 { return v.nregs }
func (v *Re) Tir_opts() uint32 { return v.opts }
func (v *Re) Tir_nltype() uint32 { return v.nltype }
func (v *Re) Tir_bsr() uint32 { return v.bsr }
func (v *Re) Tir_hascrlf() uint32 { return v.hascrlf }
func (v *Re) Tir_crfirst() uint32 { return v.crfirst }
func (v *Re) Tir_pike() bool { return v.pike }
func (v *Re) Tir_hascert() bool { return v.hascert }
func (v *Re) Tir_cert() Cert { return v.cert }
func (v *Re) Tir_haspikecert() bool { return v.haspikecert }
func (v *Re) Tir_pikecert() Cert { return v.pikecert }

func (v *Ref) Tir_num() uint32 { return v.num }
func (v *Ref) Tir_off() uint32 { return v.off }
func (v *Ref) Tir_nlen() uint32 { return v.nlen }

func (v *Region) Tir_kind() Rk { return v.kind }
func (v *Region) Tir_parent() uint32 { return v.parent }
func (v *Region) Tir_lo() uint32 { return v.lo }
func (v *Region) Tir_hi() uint32 { return v.hi }

func (v *Rep) Tir_lo() uint32 { return v.lo }
func (v *Rep) Tir_hi() uint32 { return v.hi }
func (v *Rep) Tir_greedy() bool { return v.greedy }
func (v *Rep) Tir_head() uint32 { return v.head }
func (v *Rep) Tir_body() uint32 { return v.body }
func (v *Rep) Tir_after() uint32 { return v.after }

func (v *Room) Tir_lists() uint64 { return v.lists }
func (v *Room) Tir_stk() uint64 { return v.stk }
func (v *Room) Tir_tables() uint64 { return v.tables }
func (v *Room) Tir_pool() uint64 { return v.pool }
func (v *Room) Tir_words() uint32 { return v.words }
func (v *Room) Tir_reserved() uint64 { return v.reserved }

func (v *Th) Tir_pc() uint32 { return v.pc }
func (v *Th) Tir_h() uint32 { return v.h }

func (v *Undo) Tir_slot() uint32 { return v.slot }
func (v *Undo) Tir_old() uint32 { return v.old }

func (v *Usage) Tir_cost() uint64 { return v.cost }
func (v *Usage) Tir_stack() uint32 { return v.stack }
func (v *Usage) Tir_mem() uint64 { return v.mem }

func (v *Work) Tir_ncap() uint32 { return v.ncap }
func (v *Work) Tir_nname() uint32 { return v.nname }
func (v *Work) Tir_nclass() uint32 { return v.nclass }
func (v *Work) Tir_nrep() uint32 { return v.nrep }
func (v *Work) Tir_opts() uint32 { return v.opts }
func (v *Work) Tir_err() uint32 { return v.err }
func (v *Work) Tir_erroff() uint32 { return v.erroff }
func (v *Work) Tir_root() uint32 { return v.root }
func (v *Work) Tir_hascrlf() uint32 { return v.hascrlf }
func (v *Work) Tir_crfirst() uint32 { return v.crfirst }
func (v *Work) Tir_nltype() uint32 { return v.nltype }
func (v *Work) Tir_clselems() uint32 { return v.clselems }
func (v *Work) Tir_clsrange() uint32 { return v.clsrange }
func (v *Work) Tir_clscrlf() uint32 { return v.clscrlf }
