// Code generated from engine.tir.json. DO NOT EDIT.
//
// Artifact SHA-256:
//   4b51962c6539c56954e5165f1abd3f7f7648bc87055b50e7e44e84729100a3a5
//
// The wave 1 pcre-vera engine as printed from its TIR artifact: the pattern
// parser, the bytecode compiler, and the backtracking matcher. The public
// API is the hand-written wrapper in index.mjs.
//
// The module holds the program and the printer's own tir_ helpers and
// nothing else, which is what lets TIR names be printed verbatim.
//
// A tir_Trap is thrown where TIR-SPEC.md section 12 says a checked operation
// traps. A trap is an engine bug rather than a caller error, so it fails
// loudly instead of reading undefined off the end of a typed array.

/** SHA-256 of the TIR artifact this module was printed from. */
export const artifactSha256 = "4b51962c6539c56954e5165f1abd3f7f7648bc87055b50e7e44e84729100a3a5";

/** What a checked operation throws, per TIR-SPEC.md section 12. */
export class tir_Trap extends Error {
  constructor(code, what) {
    super(`pcrevera: TIR trap ${code}: ${what}`);
    this.name = "tir_Trap";
    this.code = code;
  }
}

const tir_CAP = 9007199254740991;

function tir_i32c(x) {
  return x < 0 ? 0 : x;
}

function tir_oob(index, bound) {
  throw new tir_Trap("T-01", `index ${index} past the end of a sequence of ${bound}`);
}

/** A sequence: a backing store whose length is the capacity, plus the length. */
export class tir_Seq {
  constructor(a, n) {
    this.a = a;
    this.n = n;
  }
}

/** An inout parameter, which is always a one-field cell. */
export function tir_cell(v) {
  return { v };
}

/** A frozen bytes value over an existing Uint8Array, which it does not copy. */
export function tir_bytes(bytes) {
  return new tir_Seq(bytes, bytes.length);
}

const tir_EMPTY_U8 = new Uint8Array(0);
const tir_EMPTY_I32 = new Int32Array(0);
const tir_EMPTY_U32 = new Uint32Array(0);
const tir_EMPTY_F64 = new Float64Array(0);
const tir_EMPTY_BOOL = [];
const tir_EMPTY_OBJ = [];

function tir_mk_u8(n) {
  return new Uint8Array(n);
}

function tir_mk_i32(n) {
  return new Int32Array(n);
}

function tir_mk_u32(n) {
  return new Uint32Array(n);
}

function tir_mk_f64(n) {
  return new Float64Array(n);
}

function tir_mk_bool(n) {
  return new Array(n).fill(false);
}

function tir_mk_obj(n) {
  return new Array(n).fill(null);
}

function tir_filled(store, items) {
  for (let i = 0; i < items.length; i++) {
    store[i] = items[i];
  }
  return new tir_Seq(store, items.length);
}

function tir_bound(bound, index) {
  if (index >= bound) {
    tir_oob(index, bound);
  }
}

function tir_at(s, index) {
  if (index >= s.n) {
    tir_oob(index, s.n);
  }
  return s.a[index];
}

// Growth allocates a fresh store and copies, on the schedule of TIR-SPEC.md
// section 11; nothing here reallocates in place, because the memory accounting
// counts both stores as live at once.
function tir_grow(s, capacity, make) {
  const store = make(capacity);
  const old = s.a;
  for (let i = 0; i < s.n; i++) {
    store[i] = old[i];
  }
  s.a = store;
}

function tir_push(s, limit, make, v) {
  const n = s.n;
  if (n >= limit) {
    throw new tir_Trap("T-05", `push past the declared maximum of ${limit}`);
  }
  if (n === s.a.length) {
    let capacity = 2 * s.a.length;
    if (capacity < 4) {
      capacity = 4;
    }
    if (capacity > limit) {
      capacity = limit;
    }
    tir_grow(s, capacity, make);
  }
  s.a[n] = v;
  s.n = n + 1;
}

function tir_pop(s) {
  const n = s.n;
  if (n === 0) {
    throw new tir_Trap("T-02", "pop from an empty sequence");
  }
  s.n = n - 1;
  return s.a[n - 1];
}

function tir_truncate(s, length) {
  if (length > s.n) {
    throw new tir_Trap("T-03", `truncate to ${length}, past the length ${s.n}`);
  }
  s.n = length;
}

function tir_reserve(s, capacity, limit, make) {
  if (capacity > limit) {
    throw new tir_Trap("T-04", `reserve ${capacity}, past the declared maximum ${limit}`);
  }
  if (capacity > s.a.length) {
    tir_grow(s, capacity, make);
  }
}

// The three counter operators of TIR-SPEC.md section 6.7, checked before the
// arithmetic rather than clamped after it: a plain product of two large
// counters rounds before any comparison could look at it.
function tir_cadd(a, b) {
  return a > tir_CAP - b ? tir_CAP : a + b;
}

function tir_csub(a, b) {
  return a < b ? 0 : a - b;
}

function tir_cmul(a, b) {
  if (a === 0 || b === 0) {
    return 0;
  }
  return a > Math.floor(tir_CAP / b) ? tir_CAP : a * b;
}

// Division and remainder. The operands are non-negative for every type but
// i32, where truncation towards zero and the two overflow corners are the
// whole reason these are helpers.
function tir_div_u8(a, b, f) {
  return b === 0 ? f : Math.floor(a / b);
}

function tir_rem_u8(a, b, f) {
  return b === 0 ? f : a % b;
}

function tir_div_u32(a, b, f) {
  return b === 0 ? f : Math.floor(a / b);
}

function tir_rem_u32(a, b, f) {
  return b === 0 ? f : a % b;
}

function tir_div_counter(a, b, f) {
  return b === 0 ? f : Math.floor(a / b);
}

function tir_rem_counter(a, b, f) {
  return b === 0 ? f : a % b;
}

function tir_div_i32(a, b, f) {
  if (b === 0) {
    return f;
  }
  return Math.trunc(a / b) | 0;
}

function tir_rem_i32(a, b, f) {
  if (b === 0) {
    return f;
  }
  if (b === -1) {
    return 0;
  }
  return (a % b) | 0;
}

// enum Ar
export const ArShape = 0;
export const ArAmbiguous = 1;
export const ArOverflow = 2;
export const ArOk = 3;

// enum Bk
export const BkCost = 0;
export const BkStack = 1;
export const BkMem = 2;

// enum Cc
export const CcNotProvenLinear = 0;
export const CcLinear = 1;

// enum Cfg
export const CfgBacktrack = 0;
export const CfgPike = 1;
export const CfgMemo = 2;

// enum Cr
export const CrNoRegions = 0;
export const CrRootKind = 1;
export const CrRootParent = 2;
export const CrRootRange = 3;
export const CrTwoRoots = 4;
export const CrParentOrder = 5;
export const CrBackwards = 6;
export const CrNotNested = 7;
export const CrOverlap = 8;
export const CrNoRules = 9;
export const CrConfig = 10;
export const CrIneligible = 11;
export const CrPrices = 12;
export const CrBase = 13;
export const CrOpcode = 14;
export const CrShape = 15;
export const CrChildren = 16;
export const CrAmbiguous = 17;
export const CrOverflow = 18;
export const CrRegionWork = 19;
export const CrRegionOuts = 20;
export const CrRegionStack = 21;
export const CrRegionTrail = 22;
export const CrTotalCost = 23;
export const CrTotalStack = 24;
export const CrTotalTrail = 25;
export const CrTotalMem = 26;
export const CrNotLinear = 27;
export const CrOk = 28;

// enum Ek
export const EkErr = 0;
export const EkChar = 1;
export const EkSet = 2;
export const EkNegSet = 3;
export const EkSod = 4;
export const EkEod = 5;
export const EkEodn = 6;
export const EkWordB = 7;
export const EkNotWordB = 8;
export const EkBsr = 9;
export const EkNop = 10;

// enum Nd
export const NdNil = 0;
export const NdChar = 1;
export const NdCharCI = 2;
export const NdClass = 3;
export const NdAny = 4;
export const NdAnyNoNL = 5;
export const NdBsr = 6;
export const NdConcat = 7;
export const NdAlt = 8;
export const NdGroup = 9;
export const NdRepeat = 10;
export const NdCirc = 11;
export const NdCircM = 12;
export const NdDoll = 13;
export const NdDollE = 14;
export const NdDollM = 15;
export const NdSod = 16;
export const NdEod = 17;
export const NdEodn = 18;
export const NdWordB = 19;
export const NdNotWordB = 20;

// enum Op
export const OpChar = 0;
export const OpCharCI = 1;
export const OpClass = 2;
export const OpAny = 3;
export const OpAnyNoNL = 4;
export const OpBsr = 5;
export const OpSplit = 6;
export const OpJump = 7;
export const OpSave = 8;
export const OpCirc = 9;
export const OpCircM = 10;
export const OpDoll = 11;
export const OpDollE = 12;
export const OpDollM = 13;
export const OpSod = 14;
export const OpEod = 15;
export const OpEodn = 16;
export const OpWordB = 17;
export const OpNotWordB = 18;
export const OpRepZero = 19;
export const OpRepLoop = 20;
export const OpRepEnter = 21;
export const OpRepNext = 22;
export const OpAccept = 23;

// enum Rk
export const RkRoot = 0;
export const RkGroup = 1;
export const RkBranch = 2;
export const RkAlt = 3;
export const RkRepeat = 4;

export class Acc {
  constructor() {
    this.work = new Poly();
    this.stack = new Poly();
    this.trail = new Poly();
    this.flow = new Poly();
  }

  tir_clone() {
    const o = new Acc();
    o.work = this.work.tir_clone();
    o.stack = this.stack.tir_clone();
    o.trail = this.trail.tir_clone();
    o.flow = this.flow.tir_clone();
    return o;
  }
}

function tir_new_Acc(work, stack, trail, flow) {
  const o = new Acc();
  o.work = work;
  o.stack = stack;
  o.trail = trail;
  o.flow = flow;
  return o;
}

export class Answer {
  constructor() {
    this.status = 0;
    this.value = 0;
  }

  tir_clone() {
    const o = new Answer();
    o.status = this.status;
    o.value = this.value;
    return o;
  }
}

function tir_new_Answer(status, value) {
  const o = new Answer();
  o.status = status;
  o.value = value;
  return o;
}

export class Bound {
  constructor() {
    this.ok = false;
    this.value = 0;
  }

  tir_clone() {
    const o = new Bound();
    o.ok = this.ok;
    o.value = this.value;
    return o;
  }
}

function tir_new_Bound(ok, value) {
  const o = new Bound();
  o.ok = ok;
  o.value = value;
  return o;
}

export class Bt {
  constructor() {
    this.pc = 0;
    this.pos = 0;
    this.mark = 0;
  }

  tir_clone() {
    const o = new Bt();
    o.pc = this.pc;
    o.pos = this.pos;
    o.mark = this.mark;
    return o;
  }
}

function tir_new_Bt(pc, pos, mark) {
  const o = new Bt();
  o.pc = pc;
  o.pos = pos;
  o.mark = mark;
  return o;
}

export class Cert {
  constructor() {
    this.config = CfgBacktrack;
    this.complexity = CcNotProvenLinear;
    this.cost = new Poly();
    this.stack = new Poly();
    this.trail = new Poly();
    this.mem = new Poly();
    this.prices = new tir_Seq(tir_EMPTY_OBJ, 0);
  }

  tir_clone() {
    const o = new Cert();
    o.config = this.config;
    o.complexity = this.complexity;
    o.cost = this.cost.tir_clone();
    o.stack = this.stack.tir_clone();
    o.trail = this.trail.tir_clone();
    o.mem = this.mem.tir_clone();
    o.prices = this.prices;
    return o;
  }
}

function tir_new_Cert(config, complexity, cost, stack, trail, mem, prices) {
  const o = new Cert();
  o.config = config;
  o.complexity = complexity;
  o.cost = cost;
  o.stack = stack;
  o.trail = trail;
  o.mem = mem;
  o.prices = prices;
  return o;
}

export class Ctx {
  constructor() {
    this.re = new Re();
    this.ready = false;
    this.maxlen = 0;
    this.costcap = 0;
    this.stackcap = 0;
    this.memcap = 0;
    this.regs = new tir_Seq(tir_EMPTY_U32, 0);
    this.bt = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.trail = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.clist = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.nlist = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.stk = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.seen = new tir_Seq(tir_EMPTY_U8, 0);
    this.pool = new tir_Seq(tir_EMPTY_U32, 0);
    this.rc = new tir_Seq(tir_EMPTY_U32, 0);
    this.free = new tir_Seq(tir_EMPTY_U32, 0);
    this.slack = new tir_Seq(tir_EMPTY_U8, 0);
  }
}

function tir_new_Ctx(re, ready, maxlen, costcap, stackcap, memcap, regs, bt, trail, clist, nlist, stk, seen, pool, rc, free, slack) {
  const o = new Ctx();
  o.re = re;
  o.ready = ready;
  o.maxlen = maxlen;
  o.costcap = costcap;
  o.stackcap = stackcap;
  o.memcap = memcap;
  o.regs = regs;
  o.bt = bt;
  o.trail = trail;
  o.clist = clist;
  o.nlist = nlist;
  o.stk = stk;
  o.seen = seen;
  o.pool = pool;
  o.rc = rc;
  o.free = free;
  o.slack = slack;
  return o;
}

export class Esc {
  constructor() {
    this.kind = EkErr;
    this.val = 0;
  }

  tir_clone() {
    const o = new Esc();
    o.kind = this.kind;
    o.val = this.val;
    return o;
  }
}

function tir_new_Esc(kind, val) {
  const o = new Esc();
  o.kind = kind;
  o.val = val;
  return o;
}

export class Frame {
  constructor() {
    this.grp = 0;
    this.alt = 0;
    this.cat = 0;
    this.qual = 0;
    this.opts = 0;
    this.at = 0;
    this.unsup = 0;
  }

  tir_clone() {
    const o = new Frame();
    o.grp = this.grp;
    o.alt = this.alt;
    o.cat = this.cat;
    o.qual = this.qual;
    o.opts = this.opts;
    o.at = this.at;
    o.unsup = this.unsup;
    return o;
  }
}

function tir_new_Frame(grp, alt, cat, qual, opts, at, unsup) {
  const o = new Frame();
  o.grp = grp;
  o.alt = alt;
  o.cat = cat;
  o.qual = qual;
  o.opts = opts;
  o.at = at;
  o.unsup = unsup;
  return o;
}

export class Inst {
  constructor() {
    this.op = OpChar;
    this.arg = 0;
    this.alt = 0;
  }

  tir_clone() {
    const o = new Inst();
    o.op = this.op;
    o.arg = this.arg;
    o.alt = this.alt;
    return o;
  }
}

function tir_new_Inst(op, arg, alt) {
  const o = new Inst();
  o.op = op;
  o.arg = arg;
  o.alt = alt;
  return o;
}

export class Job {
  constructor() {
    this.node = 0;
    this.phase = 0;
    this.cur = 0;
    this.mark = 0;
    this.base = 0;
    this.here = 0;
    this.arm = 0;
  }

  tir_clone() {
    const o = new Job();
    o.node = this.node;
    o.phase = this.phase;
    o.cur = this.cur;
    o.mark = this.mark;
    o.base = this.base;
    o.here = this.here;
    o.arm = this.arm;
    return o;
  }
}

function tir_new_Job(node, phase, cur, mark, base, here, arm) {
  const o = new Job();
  o.node = node;
  o.phase = phase;
  o.cur = cur;
  o.mark = mark;
  o.base = base;
  o.here = here;
  o.arm = arm;
  return o;
}

export class NameEnt {
  constructor() {
    this.off = 0;
    this.nlen = 0;
    this.grp = 0;
  }

  tir_clone() {
    const o = new NameEnt();
    o.off = this.off;
    o.nlen = this.nlen;
    o.grp = this.grp;
    return o;
  }
}

function tir_new_NameEnt(off, nlen, grp) {
  const o = new NameEnt();
  o.off = off;
  o.nlen = nlen;
  o.grp = grp;
  return o;
}

export class Node {
  constructor() {
    this.kind = NdNil;
    this.val = 0;
    this.aux = 0;
    this.opts = 0;
    this.first = 0;
    this.last = 0;
    this.nxt = 0;
  }

  tir_clone() {
    const o = new Node();
    o.kind = this.kind;
    o.val = this.val;
    o.aux = this.aux;
    o.opts = this.opts;
    o.first = this.first;
    o.last = this.last;
    o.nxt = this.nxt;
    return o;
  }
}

function tir_new_Node(kind, val, aux, opts, first, last, nxt) {
  const o = new Node();
  o.kind = kind;
  o.val = val;
  o.aux = aux;
  o.opts = opts;
  o.first = first;
  o.last = last;
  o.nxt = nxt;
  return o;
}

export class Out {
  constructor() {
    this.err = 0;
    this.erroff = 0;
    this.re = new Re();
  }

  tir_clone() {
    const o = new Out();
    o.err = this.err;
    o.erroff = this.erroff;
    o.re = this.re.tir_clone();
    return o;
  }
}

function tir_new_Out(err, erroff, re) {
  const o = new Out();
  o.err = err;
  o.erroff = erroff;
  o.re = re;
  return o;
}

export class Poly {
  constructor() {
    this.base = 0;
    this.c0 = 0;
    this.c1 = 0;
    this.c2 = 0;
    this.c3 = 0;
    this.c4 = 0;
  }

  tir_clone() {
    const o = new Poly();
    o.base = this.base;
    o.c0 = this.c0;
    o.c1 = this.c1;
    o.c2 = this.c2;
    o.c3 = this.c3;
    o.c4 = this.c4;
    return o;
  }
}

function tir_new_Poly(base, c0, c1, c2, c3, c4) {
  const o = new Poly();
  o.base = base;
  o.c0 = c0;
  o.c1 = c1;
  o.c2 = c2;
  o.c3 = c3;
  o.c4 = c4;
  return o;
}

export class Price {
  constructor() {
    this.work = new Poly();
    this.outs = new Poly();
    this.stack = new Poly();
    this.trail = new Poly();
  }

  tir_clone() {
    const o = new Price();
    o.work = this.work.tir_clone();
    o.outs = this.outs.tir_clone();
    o.stack = this.stack.tir_clone();
    o.trail = this.trail.tir_clone();
    return o;
  }
}

function tir_new_Price(work, outs, stack, trail) {
  const o = new Price();
  o.work = work;
  o.outs = outs;
  o.stack = stack;
  o.trail = trail;
  return o;
}

export class Quant {
  constructor() {
    this.ok = false;
    this.lo = 0;
    this.hi = 0;
    this.end = 0;
  }

  tir_clone() {
    const o = new Quant();
    o.ok = this.ok;
    o.lo = this.lo;
    o.hi = this.hi;
    o.end = this.end;
    return o;
  }
}

function tir_new_Quant(ok, lo, hi, end) {
  const o = new Quant();
  o.ok = ok;
  o.lo = lo;
  o.hi = hi;
  o.end = end;
  return o;
}

export class Re {
  constructor() {
    this.code = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.classes = new tir_Seq(tir_EMPTY_U8, 0);
    this.reps = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.regions = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.names = new tir_Seq(tir_EMPTY_U8, 0);
    this.nameents = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.ncap = 0;
    this.nname = 0;
    this.nregs = 0;
    this.opts = 0;
    this.nltype = 0;
    this.bsr = 0;
    this.hascrlf = 0;
    this.crfirst = 0;
    this.pike = false;
    this.lowdec = 0;
    this.blockers = 0;
    this.lowfits = false;
    this.hascert = false;
    this.cert = new Cert();
    this.haspikecert = false;
    this.pikecert = new Cert();
  }

  tir_clone() {
    const o = new Re();
    o.code = this.code;
    o.classes = this.classes;
    o.reps = this.reps;
    o.regions = this.regions;
    o.names = this.names;
    o.nameents = this.nameents;
    o.ncap = this.ncap;
    o.nname = this.nname;
    o.nregs = this.nregs;
    o.opts = this.opts;
    o.nltype = this.nltype;
    o.bsr = this.bsr;
    o.hascrlf = this.hascrlf;
    o.crfirst = this.crfirst;
    o.pike = this.pike;
    o.lowdec = this.lowdec;
    o.blockers = this.blockers;
    o.lowfits = this.lowfits;
    o.hascert = this.hascert;
    o.cert = this.cert.tir_clone();
    o.haspikecert = this.haspikecert;
    o.pikecert = this.pikecert.tir_clone();
    return o;
  }
}

function tir_new_Re(code, classes, reps, regions, names, nameents, ncap, nname, nregs, opts, nltype, bsr, hascrlf, crfirst, pike, lowdec, blockers, lowfits, hascert, cert, haspikecert, pikecert) {
  const o = new Re();
  o.code = code;
  o.classes = classes;
  o.reps = reps;
  o.regions = regions;
  o.names = names;
  o.nameents = nameents;
  o.ncap = ncap;
  o.nname = nname;
  o.nregs = nregs;
  o.opts = opts;
  o.nltype = nltype;
  o.bsr = bsr;
  o.hascrlf = hascrlf;
  o.crfirst = crfirst;
  o.pike = pike;
  o.lowdec = lowdec;
  o.blockers = blockers;
  o.lowfits = lowfits;
  o.hascert = hascert;
  o.cert = cert;
  o.haspikecert = haspikecert;
  o.pikecert = pikecert;
  return o;
}

export class Ref {
  constructor() {
    this.num = 0;
    this.off = 0;
    this.nlen = 0;
  }

  tir_clone() {
    const o = new Ref();
    o.num = this.num;
    o.off = this.off;
    o.nlen = this.nlen;
    return o;
  }
}

function tir_new_Ref(num, off, nlen) {
  const o = new Ref();
  o.num = num;
  o.off = off;
  o.nlen = nlen;
  return o;
}

export class Region {
  constructor() {
    this.kind = RkRoot;
    this.parent = 0;
    this.lo = 0;
    this.hi = 0;
  }

  tir_clone() {
    const o = new Region();
    o.kind = this.kind;
    o.parent = this.parent;
    o.lo = this.lo;
    o.hi = this.hi;
    return o;
  }
}

function tir_new_Region(kind, parent, lo, hi) {
  const o = new Region();
  o.kind = kind;
  o.parent = parent;
  o.lo = lo;
  o.hi = hi;
  return o;
}

export class Rep {
  constructor() {
    this.lo = 0;
    this.hi = 0;
    this.greedy = false;
    this.head = 0;
    this.body = 0;
    this.after = 0;
  }

  tir_clone() {
    const o = new Rep();
    o.lo = this.lo;
    o.hi = this.hi;
    o.greedy = this.greedy;
    o.head = this.head;
    o.body = this.body;
    o.after = this.after;
    return o;
  }
}

function tir_new_Rep(lo, hi, greedy, head, body, after) {
  const o = new Rep();
  o.lo = lo;
  o.hi = hi;
  o.greedy = greedy;
  o.head = head;
  o.body = body;
  o.after = after;
  return o;
}

export class Room {
  constructor() {
    this.lists = 0;
    this.stk = 0;
    this.tables = 0;
    this.pool = 0;
    this.words = 0;
    this.reserved = 0;
  }

  tir_clone() {
    const o = new Room();
    o.lists = this.lists;
    o.stk = this.stk;
    o.tables = this.tables;
    o.pool = this.pool;
    o.words = this.words;
    o.reserved = this.reserved;
    return o;
  }
}

function tir_new_Room(lists, stk, tables, pool, words, reserved) {
  const o = new Room();
  o.lists = lists;
  o.stk = stk;
  o.tables = tables;
  o.pool = pool;
  o.words = words;
  o.reserved = reserved;
  return o;
}

export class Size {
  constructor() {
    this.code = 0;
    this.regions = 0;
    this.reps = 0;
    this.visits = 0;
    this.depth = 0;
    this.patches = 0;
    this.nullable = false;
    this.blockers = 0;
    this.needs = false;
  }

  tir_clone() {
    const o = new Size();
    o.code = this.code;
    o.regions = this.regions;
    o.reps = this.reps;
    o.visits = this.visits;
    o.depth = this.depth;
    o.patches = this.patches;
    o.nullable = this.nullable;
    o.blockers = this.blockers;
    o.needs = this.needs;
    return o;
  }
}

function tir_new_Size(code, regions, reps, visits, depth, patches, nullable, blockers, needs) {
  const o = new Size();
  o.code = code;
  o.regions = regions;
  o.reps = reps;
  o.visits = visits;
  o.depth = depth;
  o.patches = patches;
  o.nullable = nullable;
  o.blockers = blockers;
  o.needs = needs;
  return o;
}

export class Th {
  constructor() {
    this.pc = 0;
    this.h = 0;
  }

  tir_clone() {
    const o = new Th();
    o.pc = this.pc;
    o.h = this.h;
    return o;
  }
}

function tir_new_Th(pc, h) {
  const o = new Th();
  o.pc = pc;
  o.h = h;
  return o;
}

export class Undo {
  constructor() {
    this.slot = 0;
    this.old = 0;
  }

  tir_clone() {
    const o = new Undo();
    o.slot = this.slot;
    o.old = this.old;
    return o;
  }
}

function tir_new_Undo(slot, old) {
  const o = new Undo();
  o.slot = slot;
  o.old = old;
  return o;
}

export class Usage {
  constructor() {
    this.cost = 0;
    this.stack = 0;
    this.mem = 0;
  }

  tir_clone() {
    const o = new Usage();
    o.cost = this.cost;
    o.stack = this.stack;
    o.mem = this.mem;
    return o;
  }
}

function tir_new_Usage(cost, stack, mem) {
  const o = new Usage();
  o.cost = cost;
  o.stack = stack;
  o.mem = mem;
  return o;
}

export class Work {
  constructor() {
    this.nodes = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.frames = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.classes = new tir_Seq(tir_EMPTY_U8, 0);
    this.names = new tir_Seq(tir_EMPTY_U8, 0);
    this.nameents = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.code = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.reps = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.regions = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.jobs = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.patches = new tir_Seq(tir_EMPTY_U32, 0);
    this.ncap = 0;
    this.nname = 0;
    this.nclass = 0;
    this.nrep = 0;
    this.opts = 0;
    this.err = 0;
    this.erroff = 0;
    this.root = 0;
    this.refs = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.hascrlf = 0;
    this.crfirst = 0;
    this.nltype = 0;
    this.clselems = 0;
    this.clsrange = 0;
    this.clscrlf = 0;
    this.pending = new tir_Seq(tir_EMPTY_U32, 0);
    this.seen = new tir_Seq(tir_EMPTY_U8, 0);
    this.sizes = new tir_Seq(tir_EMPTY_OBJ, 0);
    this.order = new tir_Seq(tir_EMPTY_U32, 0);
    this.lowering = false;
    this.lowdec = 0;
    this.blockers = 0;
    this.lowfits = false;
    this.predicted = false;
    this.fitcode = 0;
    this.fitregion = 0;
    this.fitrep = 0;
    this.fitvisit = 0;
    this.fitjobs = 0;
    this.fitpatch = 0;
    this.peakjobs = 0;
    this.peakpatch = 0;
  }
}

function tir_new_Work(nodes, frames, classes, names, nameents, code, reps, regions, jobs, patches, ncap, nname, nclass, nrep, opts, err, erroff, root, refs, hascrlf, crfirst, nltype, clselems, clsrange, clscrlf, pending, seen, sizes, order, lowering, lowdec, blockers, lowfits, predicted, fitcode, fitregion, fitrep, fitvisit, fitjobs, fitpatch, peakjobs, peakpatch) {
  const o = new Work();
  o.nodes = nodes;
  o.frames = frames;
  o.classes = classes;
  o.names = names;
  o.nameents = nameents;
  o.code = code;
  o.reps = reps;
  o.regions = regions;
  o.jobs = jobs;
  o.patches = patches;
  o.ncap = ncap;
  o.nname = nname;
  o.nclass = nclass;
  o.nrep = nrep;
  o.opts = opts;
  o.err = err;
  o.erroff = erroff;
  o.root = root;
  o.refs = refs;
  o.hascrlf = hascrlf;
  o.crfirst = crfirst;
  o.nltype = nltype;
  o.clselems = clselems;
  o.clsrange = clsrange;
  o.clscrlf = clscrlf;
  o.pending = pending;
  o.seen = seen;
  o.sizes = sizes;
  o.order = order;
  o.lowering = lowering;
  o.lowdec = lowdec;
  o.blockers = blockers;
  o.lowfits = lowfits;
  o.predicted = predicted;
  o.fitcode = fitcode;
  o.fitregion = fitregion;
  o.fitrep = fitrep;
  o.fitvisit = fitvisit;
  o.fitjobs = fitjobs;
  o.fitpatch = fitpatch;
  o.peakjobs = peakjobs;
  o.peakpatch = peakpatch;
  return o;
}

export const BITS = new tir_Seq(new Uint8Array([1, 2, 4, 8, 16, 32, 64, 128]), 8);

export const CTYPE = new tir_Seq(new Uint8Array([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 29, 29, 29, 29, 29, 29, 29, 13, 13, 0, 0, 0, 0, 0, 0, 0, 41, 41, 41, 41, 41, 41, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 0, 0, 0, 0, 1, 0, 41, 41, 41, 41, 41, 41, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), 256);

export const FLIP = new tir_Seq(new Uint8Array([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 91, 92, 93, 94, 95, 96, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]), 256);

export const LOWER = new tir_Seq(new Uint8Array([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]), 256);

export const POSIX = new tir_Seq(new Uint8Array([5, 97, 108, 110, 117, 109, 6, 5, 97, 108, 112, 104, 97, 5, 5, 97, 115, 99, 105, 105, 7, 5, 98, 108, 97, 110, 107, 8, 5, 99, 110, 116, 114, 108, 9, 5, 100, 105, 103, 105, 116, 0, 5, 103, 114, 97, 112, 104, 10, 5, 108, 111, 119, 101, 114, 11, 5, 112, 114, 105, 110, 116, 12, 5, 112, 117, 110, 99, 116, 13, 5, 115, 112, 97, 99, 101, 2, 5, 117, 112, 112, 101, 114, 14, 4, 119, 111, 114, 100, 1, 6, 120, 100, 105, 103, 105, 116, 15]), 98);

export const SETS = new tir_Seq(new Uint8Array([0, 0, 0, 0, 0, 0, 255, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 3, 254, 255, 255, 135, 254, 255, 255, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 254, 255, 255, 7, 254, 255, 255, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 3, 254, 255, 255, 7, 254, 255, 255, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 254, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 254, 255, 255, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 254, 255, 0, 252, 1, 0, 0, 248, 1, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 254, 255, 255, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 3, 126, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), 512);

export function add_char(w, c) {
  let tmp1 = NdChar;
  let tmp2 = c;
  if (((c === 10) || (c === 13))) {
    w.v.hascrlf = 1;
  }
  if ((((w.v.opts & 1) >>> 0) !== 0)) {
    if ((tir_at(FLIP, c) !== ((c) & 255))) {
      tmp1 = NdCharCI;
      tmp2 = ((tir_at(LOWER, c)) >>> 0);
    }
  }
  attach_atom(w, tmp1, tmp2, 0);
}

export function add_child(w, parent, child) {
  if ((tir_at(w.v.nodes, parent).first === 0)) {
    const tir_t1 = parent;
    tir_bound(w.v.nodes.n, tir_t1);
    w.v.nodes.a[tir_t1].first = child;
  } else {
    let tmp1 = tir_at(w.v.nodes, parent).last;
    const tir_t2 = tmp1;
    tir_bound(w.v.nodes.n, tir_t2);
    w.v.nodes.a[tir_t2].nxt = child;
  }
  const tir_t3 = parent;
  tir_bound(w.v.nodes.n, tir_t3);
  w.v.nodes.a[tir_t3].last = child;
}

export function alloc_node(w, kind, val, aux, nopts) {
  let tmp1 = w.v.nodes.n;
  if ((tmp1 >= 8208)) {
    w.v.err = 1002;
    return 0;
  }
  tir_push(w.v.nodes, 8208, tir_mk_obj, tir_new_Node(kind, val, aux, nopts, 0, 0, 0));
  return tmp1;
}

export function apply_quant(w, lo, hi, greedy, erroff) {
  let tmp1 = ((w.v.frames.n - 1) >>> 0);
  let tmp2 = tir_at(w.v.frames, tmp1).qual;
  if ((tmp2 === 0)) {
    w.v.err = 109;
    w.v.erroff = erroff;
    return;
  }
  let tmp3 = tir_at(w.v.nodes, tmp2).kind;
  let tmp4 = true;
  const tir_t1 = tmp3;
  if (tir_t1 === NdRepeat) {
    tmp4 = false;
  } else if (tir_t1 === NdCirc) {
    tmp4 = false;
  } else if (tir_t1 === NdCircM) {
    tmp4 = false;
  } else if (tir_t1 === NdDoll) {
    tmp4 = false;
  } else if (tir_t1 === NdDollE) {
    tmp4 = false;
  } else if (tir_t1 === NdDollM) {
    tmp4 = false;
  } else if (tir_t1 === NdSod) {
    tmp4 = false;
  } else if (tir_t1 === NdEod) {
    tmp4 = false;
  } else if (tir_t1 === NdEodn) {
    tmp4 = false;
  } else if (tir_t1 === NdWordB) {
    tmp4 = false;
  } else if (tir_t1 === NdNotWordB) {
    tmp4 = false;
  } else {
    // nothing
  }
  if ((!tmp4)) {
    w.v.err = 109;
    w.v.erroff = erroff;
    return;
  }
  let tmp5 = 0;
  let tmp6 = tir_at(w.v.nodes, tmp2).tir_clone();
  const tir_t2 = alloc_node(w, tmp6.kind, tmp6.val, tmp6.aux, tmp6.opts);
  tmp5 = tir_t2;
  if ((w.v.err !== 0)) {
    return;
  }
  const tir_t3 = tmp5;
  tir_bound(w.v.nodes.n, tir_t3);
  w.v.nodes.a[tir_t3].first = tmp6.first;
  const tir_t4 = tmp5;
  tir_bound(w.v.nodes.n, tir_t4);
  w.v.nodes.a[tir_t4].last = tmp6.last;
  const tir_t5 = tmp2;
  tir_bound(w.v.nodes.n, tir_t5);
  w.v.nodes.a[tir_t5].kind = NdRepeat;
  const tir_t6 = tmp2;
  tir_bound(w.v.nodes.n, tir_t6);
  w.v.nodes.a[tir_t6].val = lo;
  const tir_t7 = tmp2;
  tir_bound(w.v.nodes.n, tir_t7);
  w.v.nodes.a[tir_t7].aux = hi;
  const tir_t8 = tmp2;
  tir_bound(w.v.nodes.n, tir_t8);
  w.v.nodes.a[tir_t8].opts = (greedy ? 1 : 0);
  const tir_t9 = tmp2;
  tir_bound(w.v.nodes.n, tir_t9);
  w.v.nodes.a[tir_t9].first = tmp5;
  const tir_t10 = tmp2;
  tir_bound(w.v.nodes.n, tir_t10);
  w.v.nodes.a[tir_t10].last = tmp5;
}

export function at_line_end(subj, pos, nltype) {
  let tmp1 = subj.n;
  if ((pos >= tmp1)) {
    return true;
  }
  let tmp2 = 0;
  const tir_t1 = newline_at(subj, pos, nltype);
  tmp2 = tir_t1;
  return ((tmp2 !== 0) && (tmp1 === ((pos + tmp2) >>> 0)));
}

export function attach_atom(w, kind, val, aux) {
  let tmp1 = 0;
  let tmp2 = kind;
  let tmp3 = val;
  let tmp4 = aux;
  const tir_t1 = alloc_node(w, tmp2, tmp3, tmp4, 0);
  tmp1 = tir_t1;
  if ((w.v.err !== 0)) {
    return;
  }
  let tmp5 = ((w.v.frames.n - 1) >>> 0);
  let tmp6 = tir_at(w.v.frames, tmp5).cat;
  add_child(w, tmp6, tmp1);
  const tir_t2 = tmp5;
  tir_bound(w.v.frames.n, tir_t2);
  w.v.frames.a[tir_t2].qual = tmp1;
}

export function attach_escape(w, esc) {
  const tir_t1 = esc.kind;
  if (tir_t1 === EkChar) {
    let tmp1 = esc.val;
    add_char(w, tmp1);
  } else if (tir_t1 === EkSet) {
    class_from_set(w, esc.val, false);
  } else if (tir_t1 === EkNegSet) {
    class_from_set(w, esc.val, true);
  } else if (tir_t1 === EkSod) {
    attach_atom(w, NdSod, 0, 0);
  } else if (tir_t1 === EkEod) {
    attach_atom(w, NdEod, 0, 0);
  } else if (tir_t1 === EkEodn) {
    attach_atom(w, NdEodn, 0, 0);
  } else if (tir_t1 === EkWordB) {
    attach_atom(w, NdWordB, 0, 0);
  } else if (tir_t1 === EkNotWordB) {
    attach_atom(w, NdNotWordB, 0, 0);
  } else if (tir_t1 === EkBsr) {
    attach_atom(w, NdBsr, 0, 0);
  } else if (tir_t1 === EkNop) {
    attach_atom(w, NdNil, 0, 0);
  } else {
    // nothing
  }
}

export function bound_add(a, b) {
  if (((!a.ok) || (!b.ok))) {
    return tir_new_Bound(false, 0);
  }
  let over = false;
  let total = 0;
  const tir_t1 = tir_cell(over);
  const tir_t2 = sat_add(a.value, b.value, tir_t1);
  over = tir_t1.v;
  total = tir_t2;
  if (over) {
    return tir_new_Bound(false, 0);
  }
  return tir_new_Bound(true, total);
}

export function bound_mul(a, b) {
  if (((!a.ok) || (!b.ok))) {
    return tir_new_Bound(false, 0);
  }
  let over = false;
  let total = 0;
  const tir_t1 = tir_cell(over);
  const tir_t2 = sat_mul(a.value, b.value, tir_t1);
  over = tir_t1.v;
  total = tir_t2;
  if (over) {
    return tir_new_Bound(false, 0);
  }
  return tir_new_Bound(true, total);
}

export function bound_pow(base, exp) {
  if ((base === 1)) {
    return tir_new_Bound(true, 1);
  }
  if ((base === 0)) {
    if ((exp === 0)) {
      return tir_new_Bound(true, 1);
    }
    return tir_new_Bound(true, 0);
  }
  let out = tir_new_Bound(true, 1);
  let i = 0;
  let one = new Bound();
  while (((i < exp) && out.ok)) {
    const tir_t1 = bound_mul(out.tir_clone(), tir_new_Bound(true, base));
    one = tir_t1;
    out = one.tir_clone();
    i = tir_cadd(i, 1);
  }
  return out.tir_clone();
}

export function bsr_at(subj, pos, bsr) {
  let tmp1 = subj.n;
  if ((pos >= tmp1)) {
    return 0;
  }
  let tmp2 = tir_at(subj, pos);
  if ((tmp2 === 13)) {
    if (((tmp1 > ((pos + 1) >>> 0)) && (tir_at(subj, ((pos + 1) >>> 0)) === 10))) {
      return 2;
    }
    return 1;
  }
  if ((tmp2 === 10)) {
    return 1;
  }
  if ((bsr === 1)) {
    return 0;
  }
  if (((tmp2 === 11) || ((tmp2 === 12) || (tmp2 === 133)))) {
    return 1;
  }
  return 0;
}

export function bt_match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use) {
  let regs = new tir_Seq(tir_EMPTY_U32, 0);
  let bt = new tir_Seq(tir_EMPTY_OBJ, 0);
  let trail = new tir_Seq(tir_EMPTY_OBJ, 0);
  let tmp1 = 1;
  const tir_t1 = tir_cell(regs);
  const tir_t2 = tir_cell(bt);
  const tir_t3 = tir_cell(trail);
  const tir_t4 = bt_run(re.tir_clone(), subj, start, mopts, costlimit, stacklimit, memlimit, tir_t1, tir_t2, tir_t3, ov, use);
  regs = tir_t1.v;
  bt = tir_t2.v;
  trail = tir_t3.v;
  tmp1 = tir_t4;
  return tmp1;
}

export function bt_run(re, subj, start, mopts, costlimit, stacklimit, memlimit, regs, bt, trail, ov, use) {
  let tmp1 = subj.n;
  let tmp2 = 0;
  let tmp3 = 0;
  let tmp4 = 0;
  let tmp5 = 0;
  use.v.cost = tmp2;
  use.v.stack = tmp5;
  use.v.mem = tmp4;
  if ((start > tmp1)) {
    return 3;
  }
  let code = re.code;
  let classes = re.classes;
  let reps = re.reps;
  let tmp6 = re.nltype;
  let tmp7 = re.bsr;
  let tmp8 = re.ncap;
  let tmp9 = re.nregs;
  let tmp10 = ((Math.imul(((tmp8 + 1) >>> 0), 2)) >>> 0);
  let tmp11 = tmp10;
  let tmp12 = ((((re.opts & 32) >>> 0) !== 0) || (((mopts & 16) >>> 0) !== 0));
  let tmp13 = (((mopts & 4) >>> 0) !== 0);
  let tmp14 = (((mopts & 8) >>> 0) !== 0);
  let tmp15 = (re.hascrlf === 0);
  let tmp16 = ((tmp6 === 2) || ((tmp6 === 3) || (tmp6 === 4)));
  let tmp17 = (((mopts & 1) >>> 0) !== 0);
  let tmp18 = (((mopts & 2) >>> 0) !== 0);
  let tmp19 = tir_cmul((((tmp9 + tmp10) >>> 0)), 4);
  if (((tmp19 > memlimit) || (tmp19 > costlimit))) {
    return 2;
  }
  tmp3 = tmp19;
  tmp4 = tmp19;
  tmp2 = tmp19;
  tir_reserve(regs.v, tmp9, 8704, tir_mk_u32);
  tir_truncate(regs.v, 0);
  tir_truncate(bt.v, 0);
  tir_truncate(trail.v, 0);
  tir_reserve(ov.v, tmp10, 512, tir_mk_u32);
  let tmp20 = 0;
  while ((tmp20 < tmp9)) {
    tir_push(regs.v, 8704, tir_mk_u32, 4294967295);
    tmp20 = ((tmp20 + 1) >>> 0);
  }
  tir_truncate(ov.v, 0);
  tmp20 = 0;
  while ((tmp20 < tmp10)) {
    tir_push(ov.v, 512, tir_mk_u32, 4294967295);
    tmp20 = ((tmp20 + 1) >>> 0);
  }
  let tmp21 = start;
  let tmp22 = 1;
  let tmp23 = true;
  let tmp24 = false;
  while (tmp23) {
    let tmp25 = tir_cmul((tmp9), 4);
    if ((tmp25 > tir_csub(costlimit, tmp2))) {
      tmp22 = 2;
      tmp23 = false;
      continue;
    }
    tmp2 = tir_cadd(tmp2, tmp25);
    let tmp26 = 0;
    while ((tmp26 < tmp9)) {
      const tir_t1 = tmp26;
      tir_bound(regs.v.n, tir_t1);
      regs.v.a[tir_t1] = 4294967295;
      tmp26 = ((tmp26 + 1) >>> 0);
    }
    tir_truncate(bt.v, 0);
    tir_truncate(trail.v, 0);
    let tmp27 = 0;
    let tmp28 = tmp21;
    let tmp29 = true;
    let tmp30 = false;
    let tmp31 = false;
    while (tmp29) {
      if ((tmp2 >= costlimit)) {
        tmp22 = 2;
        tmp23 = false;
        tmp29 = false;
        continue;
      }
      tmp2 = tir_cadd(tmp2, 1);
      let tmp32 = tir_at(code, tmp27).tir_clone();
      const tir_t2 = tmp32.op;
      if (tir_t2 === OpChar) {
        if (((tmp28 < tmp1) && (tir_at(subj, tmp28) === ((tmp32.arg) & 255)))) {
          tmp28 = ((tmp28 + 1) >>> 0);
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpCharCI) {
        if (((tmp28 < tmp1) && (tir_at(LOWER, ((tir_at(subj, tmp28)) >>> 0)) === ((tmp32.arg) & 255)))) {
          tmp28 = ((tmp28 + 1) >>> 0);
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpClass) {
        let tmp33 = false;
        if ((tmp28 < tmp1)) {
          const tir_t3 = class_has(classes, tmp32.arg, tir_at(subj, tmp28));
          tmp33 = tir_t3;
        }
        if (((tmp28 < tmp1) && tmp33)) {
          tmp28 = ((tmp28 + 1) >>> 0);
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpAny) {
        if (((tmp28 < tmp1) && true)) {
          tmp28 = ((tmp28 + 1) >>> 0);
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpAnyNoNL) {
        let tmp34 = 0;
        if ((tmp28 < tmp1)) {
          const tir_t4 = newline_at(subj, tmp28, tmp6);
          tmp34 = tir_t4;
        }
        if (((tmp28 < tmp1) && (tmp34 === 0))) {
          tmp28 = ((tmp28 + 1) >>> 0);
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpBsr) {
        let tmp35 = 0;
        const tir_t5 = bsr_at(subj, tmp28, tmp7);
        tmp35 = tir_t5;
        if ((tmp35 !== 0)) {
          tmp28 = ((tmp28 + tmp35) >>> 0);
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpSplit) {
        let tmp36 = trail.v.n;
        const tir_t6 = tir_cell(tmp3);
        const tir_t7 = tir_cell(tmp4);
        const tir_t8 = tir_cell(tmp2);
        const tir_t9 = push_bt(bt, tir_t6, tir_t7, tir_t8, memlimit, costlimit, stacklimit, tmp32.alt, tmp28, tmp36);
        tmp3 = tir_t6.v;
        tmp4 = tir_t7.v;
        tmp2 = tir_t8.v;
        tmp24 = tir_t9;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        } else {
          if ((tmp5 < bt.v.n)) {
            tmp5 = bt.v.n;
          }
        }
        tmp27 = tmp32.arg;
      } else if (tir_t2 === OpJump) {
        tmp27 = tmp32.arg;
      } else if (tir_t2 === OpSave) {
        const tir_t10 = tir_cell(tmp3);
        const tir_t11 = tir_cell(tmp4);
        const tir_t12 = tir_cell(tmp2);
        const tir_t13 = write_reg(regs, trail, tir_t10, tir_t11, tir_t12, memlimit, costlimit, bt.v.n, tmp32.arg, tmp28);
        tmp3 = tir_t10.v;
        tmp4 = tir_t11.v;
        tmp2 = tir_t12.v;
        tmp24 = tir_t13;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        }
        tmp27 = ((tmp27 + 1) >>> 0);
      } else if (tir_t2 === OpCirc) {
        if (((tmp28 === 0) && (!tmp17))) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpCircM) {
        let tmp37 = (!tmp17);
        if ((tmp28 !== 0)) {
          let tmp38 = 0;
          const tir_t14 = newline_before(subj, tmp28, tmp6);
          tmp38 = tir_t14;
          tmp37 = ((tmp28 !== tmp1) && (tmp38 !== 0));
        }
        if (tmp37) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpDoll) {
        let tmp39 = false;
        const tir_t15 = at_line_end(subj, tmp28, tmp6);
        tmp39 = tir_t15;
        if (((!tmp18) && tmp39)) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpDollE) {
        if (((!tmp18) && (tmp28 === tmp1))) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpDollM) {
        let tmp40 = (!tmp18);
        if ((tmp28 < tmp1)) {
          let tmp41 = 0;
          const tir_t16 = newline_at(subj, tmp28, tmp6);
          tmp41 = tir_t16;
          tmp40 = (tmp41 !== 0);
        }
        if (tmp40) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpSod) {
        if ((tmp28 === 0)) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpEod) {
        if ((tmp28 === tmp1)) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpEodn) {
        let tmp42 = false;
        const tir_t17 = at_line_end(subj, tmp28, tmp6);
        tmp42 = tir_t17;
        if (tmp42) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpWordB) {
        const tir_t18 = word_edge(subj, tmp28);
        tmp24 = tir_t18;
        if (tmp24) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpNotWordB) {
        const tir_t19 = word_edge(subj, tmp28);
        tmp24 = tir_t19;
        if ((!tmp24)) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpRepZero) {
        const tir_t20 = tir_cell(tmp3);
        const tir_t21 = tir_cell(tmp4);
        const tir_t22 = tir_cell(tmp2);
        const tir_t23 = write_reg(regs, trail, tir_t20, tir_t21, tir_t22, memlimit, costlimit, bt.v.n, ((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0), 0);
        tmp3 = tir_t20.v;
        tmp4 = tir_t21.v;
        tmp2 = tir_t22.v;
        tmp24 = tir_t23;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        }
        tmp27 = ((tmp27 + 1) >>> 0);
      } else if (tir_t2 === OpRepEnter) {
        const tir_t24 = tir_cell(tmp3);
        const tir_t25 = tir_cell(tmp4);
        const tir_t26 = tir_cell(tmp2);
        const tir_t27 = write_reg(regs, trail, tir_t24, tir_t25, tir_t26, memlimit, costlimit, bt.v.n, ((((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0) + 1) >>> 0), tmp28);
        tmp3 = tir_t24.v;
        tmp4 = tir_t25.v;
        tmp2 = tir_t26.v;
        tmp24 = tir_t27;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        }
        tmp27 = ((tmp27 + 1) >>> 0);
      } else if (tir_t2 === OpRepLoop) {
        let tmp43 = tir_at(reps, tmp32.arg).tir_clone();
        let tmp44 = tir_at(regs.v, ((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0));
        if ((tmp44 < tmp43.lo)) {
          tmp27 = tmp43.body;
        } else {
          if ((tmp44 >= tmp43.hi)) {
            tmp27 = tmp43.after;
          } else {
            if (tmp43.greedy) {
              let tmp45 = trail.v.n;
              const tir_t28 = tir_cell(tmp3);
              const tir_t29 = tir_cell(tmp4);
              const tir_t30 = tir_cell(tmp2);
              const tir_t31 = push_bt(bt, tir_t28, tir_t29, tir_t30, memlimit, costlimit, stacklimit, tmp43.after, tmp28, tmp45);
              tmp3 = tir_t28.v;
              tmp4 = tir_t29.v;
              tmp2 = tir_t30.v;
              tmp24 = tir_t31;
              if ((!tmp24)) {
                tmp22 = 2;
                tmp23 = false;
                tmp29 = false;
              } else {
                if ((tmp5 < bt.v.n)) {
                  tmp5 = bt.v.n;
                }
              }
              tmp27 = tmp43.body;
            } else {
              let tmp46 = trail.v.n;
              const tir_t32 = tir_cell(tmp3);
              const tir_t33 = tir_cell(tmp4);
              const tir_t34 = tir_cell(tmp2);
              const tir_t35 = push_bt(bt, tir_t32, tir_t33, tir_t34, memlimit, costlimit, stacklimit, tmp43.body, tmp28, tmp46);
              tmp3 = tir_t32.v;
              tmp4 = tir_t33.v;
              tmp2 = tir_t34.v;
              tmp24 = tir_t35;
              if ((!tmp24)) {
                tmp22 = 2;
                tmp23 = false;
                tmp29 = false;
              } else {
                if ((tmp5 < bt.v.n)) {
                  tmp5 = bt.v.n;
                }
              }
              tmp27 = tmp43.after;
            }
          }
        }
      } else if (tir_t2 === OpRepNext) {
        let tmp47 = tir_at(reps, tmp32.arg).tir_clone();
        let tmp48 = ((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0);
        let tmp49 = ((tir_at(regs.v, tmp48) + 1) >>> 0);
        let tmp50 = tir_at(regs.v, ((tmp48 + 1) >>> 0));
        const tir_t36 = tir_cell(tmp3);
        const tir_t37 = tir_cell(tmp4);
        const tir_t38 = tir_cell(tmp2);
        const tir_t39 = write_reg(regs, trail, tir_t36, tir_t37, tir_t38, memlimit, costlimit, bt.v.n, tmp48, tmp49);
        tmp3 = tir_t36.v;
        tmp4 = tir_t37.v;
        tmp2 = tir_t38.v;
        tmp24 = tir_t39;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        }
        if (((tmp47.hi === 4294967295) && ((tmp28 === tmp50) && (tmp49 >= tmp47.lo)))) {
          tmp27 = tmp47.after;
        } else {
          tmp27 = tmp47.head;
        }
      } else if (tir_t2 === OpAccept) {
        let tmp51 = (tmp28 === tmp21);
        let tmp52 = (tmp51 && (tmp13 || (tmp14 && (tmp21 === start))));
        if (tmp52) {
          tmp30 = true;
        } else {
          const tir_t40 = 0;
          tir_bound(regs.v.n, tir_t40);
          regs.v.a[tir_t40] = tmp21;
          const tir_t41 = 1;
          tir_bound(regs.v.n, tir_t41);
          regs.v.a[tir_t41] = tmp28;
          tmp31 = true;
          tmp29 = false;
        }
      }
      if (tmp30) {
        if ((bt.v.n === 0)) {
          tmp29 = false;
          tir_truncate(trail.v, 0);
        } else {
          let tmp53 = new Bt();
          tmp53 = tir_pop(bt.v);
          tmp27 = tmp53.pc;
          tmp28 = tmp53.pos;
          let tmp54 = tir_cmul(tir_csub((trail.v.n), (tmp53.mark)), 4);
          if ((tmp54 > tir_csub(costlimit, tmp2))) {
            tmp22 = 2;
            tmp23 = false;
            tmp29 = false;
          } else {
            tmp2 = tir_cadd(tmp2, tmp54);
            while ((tmp53.mark < trail.v.n)) {
              let tmp55 = new Undo();
              tmp55 = tir_pop(trail.v);
              const tir_t42 = tmp55.slot;
              tir_bound(regs.v.n, tir_t42);
              regs.v.a[tir_t42] = tmp55.old;
            }
            if ((bt.v.n === 0)) {
              tir_truncate(trail.v, 0);
            }
            tmp30 = false;
          }
        }
      }
    }
    if (tmp31) {
      tmp22 = 0;
      tmp23 = false;
      continue;
    }
    if ((!tmp23)) {
      continue;
    }
    if ((tmp12 || (tmp21 >= tmp1))) {
      tmp23 = false;
      continue;
    }
    tmp21 = ((tmp21 + 1) >>> 0);
    if (((tmp16 && (tmp15 && (re.crfirst !== 0))) && ((tir_at(subj, ((tmp21 - 1) >>> 0)) === 13) && ((tmp21 < tmp1) && (tir_at(subj, tmp21) === 10))))) {
      tmp21 = ((tmp21 + 1) >>> 0);
    }
  }
  if ((tmp22 === 0)) {
    let tmp56 = tir_cmul((tmp10), 4);
    if ((tmp56 > tir_csub(costlimit, tmp2))) {
      tmp22 = 2;
    } else {
      tmp2 = tir_cadd(tmp2, tmp56);
      let tmp57 = 0;
      while ((tmp57 < tmp10)) {
        const tir_t43 = tmp57;
        tir_bound(ov.v.n, tir_t43);
        ov.v.a[tir_t43] = tir_at(regs.v, tmp57);
        tmp57 = ((tmp57 + 1) >>> 0);
      }
    }
  }
  use.v.cost = tmp2;
  use.v.stack = tmp5;
  use.v.mem = tmp4;
  return tmp22;
}

export function cert_bound(cert, kind, n) {
  let which = new Poly();
  let ceiling = 9007199254740991;
  let known = false;
  const tir_t1 = kind;
  if (tir_t1 === BkCost) {
    which = cert.cost.tir_clone();
    known = true;
  } else if (tir_t1 === BkStack) {
    which = cert.stack.tir_clone();
    ceiling = 178956970;
    known = true;
  } else if (tir_t1 === BkMem) {
    which = cert.mem.tir_clone();
    ceiling = 2147483647;
    known = true;
  }
  if ((!known)) {
    return tir_new_Bound(false, 0);
  }
  let out = new Bound();
  const tir_t2 = poly_value(which.tir_clone(), n);
  out = tir_t2;
  if ((out.ok && (out.value > ceiling))) {
    return tir_new_Bound(false, 0);
  }
  return out.tir_clone();
}

export function cert_build(re, cert) {
  let over = false;
  let regions = re.regions;
  let total = regions.n;
  if ((total === 0)) {
    return ArShape;
  }
  let prices = new tir_Seq(tir_EMPTY_OBJ, 0);
  let kids = new tir_Seq(tir_EMPTY_U32, 0);
  let sibs = new tir_Seq(tir_EMPTY_U32, 0);
  let stop = re.code.n;
  let i = 0;
  while ((i < total)) {
    let tmp1 = tir_at(regions, i).tir_clone();
    if (((tmp1.lo > tmp1.hi) || (tmp1.hi > stop))) {
      return ArShape;
    }
    if (((i > 0) && (tmp1.parent >= i))) {
      return ArShape;
    }
    tir_push(prices, 8208, tir_mk_obj, tir_new_Price(tir_new_Poly(1, 0, 0, 0, 0, 0), tir_new_Poly(1, 0, 0, 0, 0, 0), tir_new_Poly(1, 0, 0, 0, 0, 0), tir_new_Poly(1, 0, 0, 0, 0, 0)));
    i = ((i + 1) >>> 0);
  }
  const tir_t1 = tir_cell(kids);
  const tir_t2 = tir_cell(sibs);
  region_kids(regions, tir_t1, tir_t2);
  kids = tir_t1.v;
  sibs = tir_t2.v;
  i = total;
  while ((i > 0)) {
    i = ((i - 1) >>> 0);
    let tmp2 = tir_at(regions, i).tir_clone();
    let tmp3 = new Acc();
    let tmp4 = tir_at(kids, i);
    let tmp5 = ArShape;
    const tir_t3 = tmp2.kind;
    if (tir_t3 === RkRoot) {
      tmp3.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
      const tir_t4 = tir_cell(prices);
      const tir_t5 = tir_cell(sibs);
      const tir_t6 = tir_cell(tmp3);
      const tir_t7 = tir_cell(over);
      const tir_t8 = price_span(re.code, regions, tir_t4, tir_t5, tmp2.lo, tmp2.hi, tmp4, tir_t6, tir_t7);
      prices = tir_t4.v;
      sibs = tir_t5.v;
      tmp3 = tir_t6.v;
      over = tir_t7.v;
      tmp5 = tir_t8;
    } else if (tir_t3 === RkGroup) {
      tmp3.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
      const tir_t9 = tir_cell(prices);
      const tir_t10 = tir_cell(sibs);
      const tir_t11 = tir_cell(tmp3);
      const tir_t12 = tir_cell(over);
      const tir_t13 = price_span(re.code, regions, tir_t9, tir_t10, tmp2.lo, tmp2.hi, tmp4, tir_t11, tir_t12);
      prices = tir_t9.v;
      sibs = tir_t10.v;
      tmp3 = tir_t11.v;
      over = tir_t12.v;
      tmp5 = tir_t13;
    } else if (tir_t3 === RkBranch) {
      tmp3.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
      const tir_t14 = tir_cell(prices);
      const tir_t15 = tir_cell(sibs);
      const tir_t16 = tir_cell(tmp3);
      const tir_t17 = tir_cell(over);
      const tir_t18 = price_span(re.code, regions, tir_t14, tir_t15, tmp2.lo, tmp2.hi, tmp4, tir_t16, tir_t17);
      prices = tir_t14.v;
      sibs = tir_t15.v;
      tmp3 = tir_t16.v;
      over = tir_t17.v;
      tmp5 = tir_t18;
    } else if (tir_t3 === RkAlt) {
      const tir_t19 = tir_cell(prices);
      const tir_t20 = tir_cell(sibs);
      const tir_t21 = tir_cell(tmp3);
      const tir_t22 = tir_cell(over);
      const tir_t23 = price_alt(tir_t19, tir_t20, tmp4, tir_t21, tir_t22);
      prices = tir_t19.v;
      sibs = tir_t20.v;
      tmp3 = tir_t21.v;
      over = tir_t22.v;
      tmp5 = tir_t23;
    } else if (tir_t3 === RkRepeat) {
      const tir_t24 = tir_cell(prices);
      const tir_t25 = tir_cell(sibs);
      const tir_t26 = tir_cell(tmp3);
      const tir_t27 = tir_cell(over);
      const tir_t28 = price_repeat(re.code, re.reps, regions, tir_t24, tir_t25, i, tmp4, tir_t26, tir_t27);
      prices = tir_t24.v;
      sibs = tir_t25.v;
      tmp3 = tir_t26.v;
      over = tir_t27.v;
      tmp5 = tir_t28;
    }
    if ((tmp5 !== ArOk)) {
      return tmp5;
    }
    if (over) {
      return ArOverflow;
    }
    const tir_t29 = i;
    tir_bound(prices.n, tir_t29);
    prices.a[tir_t29] = tir_new_Price(tmp3.work.tir_clone(), tmp3.flow.tir_clone(), tmp3.stack.tir_clone(), tmp3.trail.tir_clone());
  }
  let root = tir_at(prices, 0).tir_clone();
  const tir_t30 = tir_cell(over);
  price_call(re.tir_clone(), root.tir_clone(), cert, tir_t30);
  over = tir_t30.v;
  if (over) {
    return ArOverflow;
  }
  cert.v.config = CfgBacktrack;
  cert.v.complexity = CcNotProvenLinear;
  if (((((cert.v.cost.base === 1) && (cert.v.cost.c2 === 0)) && (cert.v.cost.c3 === 0)) && (cert.v.cost.c4 === 0))) {
    cert.v.complexity = CcLinear;
  }
  cert.v.prices = prices;
  prices = new tir_Seq(tir_EMPTY_OBJ, 0);
  return ArOk;
}

export function cert_check(re, config, cert) {
  let over = false;
  if ((config === CfgPike)) {
    let answered = CrNoRules;
    const tir_t1 = pike_check(re.tir_clone(), cert.tir_clone());
    answered = tir_t1;
    return answered;
  }
  if ((config !== CfgBacktrack)) {
    return CrNoRules;
  }
  if ((cert.config !== config)) {
    return CrConfig;
  }
  let shape = CrOk;
  const tir_t2 = cert_shape(re.tir_clone());
  shape = tir_t2;
  if ((shape !== CrOk)) {
    return shape;
  }
  let code = re.code;
  let regions = re.regions;
  let prices = cert.prices;
  let total = regions.n;
  if ((total !== prices.n)) {
    return CrPrices;
  }
  if ((cert.cost.base === 0)) {
    return CrBase;
  }
  if ((cert.stack.base === 0)) {
    return CrBase;
  }
  if ((cert.trail.base === 0)) {
    return CrBase;
  }
  if ((cert.mem.base === 0)) {
    return CrBase;
  }
  if (((cert.complexity !== CcNotProvenLinear) && (cert.complexity !== CcLinear))) {
    return CrShape;
  }
  if ((cert.complexity === CcLinear)) {
    if ((!((((cert.cost.base === 1) && (cert.cost.c2 === 0)) && (cert.cost.c3 === 0)) && (cert.cost.c4 === 0)))) {
      return CrNotLinear;
    }
  }
  let i = 0;
  while ((i < total)) {
    let tmp1 = tir_at(prices, i).tir_clone();
    if ((tmp1.work.base === 0)) {
      return CrBase;
    }
    if ((tmp1.outs.base === 0)) {
      return CrBase;
    }
    if ((tmp1.stack.base === 0)) {
      return CrBase;
    }
    if ((tmp1.trail.base === 0)) {
      return CrBase;
    }
    i = ((i + 1) >>> 0);
  }
  let kids = new tir_Seq(tir_EMPTY_U32, 0);
  let sibs = new tir_Seq(tir_EMPTY_U32, 0);
  const tir_t3 = tir_cell(kids);
  const tir_t4 = tir_cell(sibs);
  region_kids(regions, tir_t3, tir_t4);
  kids = tir_t3.v;
  sibs = tir_t4.v;
  i = 0;
  while ((i < total)) {
    let tmp2 = tir_at(regions, i).tir_clone();
    let tmp3 = new Acc();
    let tmp4 = tir_at(kids, i);
    let tmp5 = CrShape;
    const tir_t5 = tmp2.kind;
    if (tir_t5 === RkRoot) {
      tmp3.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
      const tir_t6 = tir_cell(sibs);
      const tir_t7 = tir_cell(tmp3);
      const tir_t8 = tir_cell(over);
      const tir_t9 = scan_span(code, regions, prices, tir_t6, tmp2.lo, tmp2.hi, tmp4, tir_t7, tir_t8);
      sibs = tir_t6.v;
      tmp3 = tir_t7.v;
      over = tir_t8.v;
      tmp5 = tir_t9;
    } else if (tir_t5 === RkGroup) {
      tmp3.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
      const tir_t10 = tir_cell(sibs);
      const tir_t11 = tir_cell(tmp3);
      const tir_t12 = tir_cell(over);
      const tir_t13 = scan_span(code, regions, prices, tir_t10, tmp2.lo, tmp2.hi, tmp4, tir_t11, tir_t12);
      sibs = tir_t10.v;
      tmp3 = tir_t11.v;
      over = tir_t12.v;
      tmp5 = tir_t13;
    } else if (tir_t5 === RkBranch) {
      tmp3.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
      tmp3.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
      const tir_t14 = tir_cell(sibs);
      const tir_t15 = tir_cell(tmp3);
      const tir_t16 = tir_cell(over);
      const tir_t17 = scan_span(code, regions, prices, tir_t14, tmp2.lo, tmp2.hi, tmp4, tir_t15, tir_t16);
      sibs = tir_t14.v;
      tmp3 = tir_t15.v;
      over = tir_t16.v;
      tmp5 = tir_t17;
    } else if (tir_t5 === RkAlt) {
      const tir_t18 = tir_cell(sibs);
      const tir_t19 = tir_cell(tmp3);
      const tir_t20 = tir_cell(over);
      const tir_t21 = scan_alt(prices, tir_t18, tmp4, tir_t19, tir_t20);
      sibs = tir_t18.v;
      tmp3 = tir_t19.v;
      over = tir_t20.v;
      tmp5 = tir_t21;
    } else if (tir_t5 === RkRepeat) {
      const tir_t22 = tir_cell(sibs);
      const tir_t23 = tir_cell(tmp3);
      const tir_t24 = tir_cell(over);
      const tir_t25 = scan_repeat(code, re.reps, regions, prices, tir_t22, i, tmp4, tir_t23, tir_t24);
      sibs = tir_t22.v;
      tmp3 = tir_t23.v;
      over = tir_t24.v;
      tmp5 = tir_t25;
    }
    if ((tmp5 !== CrOk)) {
      return tmp5;
    }
    if (over) {
      return CrOverflow;
    }
    let tmp6 = false;
    let tmp7 = tir_at(prices, i).tir_clone();
    const tir_t26 = poly_ge(tmp7.work.tir_clone(), tmp3.work.tir_clone());
    tmp6 = tir_t26;
    if ((!tmp6)) {
      return CrRegionWork;
    }
    const tir_t27 = poly_ge(tmp7.outs.tir_clone(), tmp3.flow.tir_clone());
    tmp6 = tir_t27;
    if ((!tmp6)) {
      return CrRegionOuts;
    }
    const tir_t28 = poly_ge(tmp7.stack.tir_clone(), tmp3.stack.tir_clone());
    tmp6 = tir_t28;
    if ((!tmp6)) {
      return CrRegionStack;
    }
    const tir_t29 = poly_ge(tmp7.trail.tir_clone(), tmp3.trail.tir_clone());
    tmp6 = tir_t29;
    if ((!tmp6)) {
      return CrRegionTrail;
    }
    i = ((i + 1) >>> 0);
  }
  let whole = tir_at(prices, 0).tir_clone();
  let charged = CrOk;
  const tir_t30 = tir_cell(over);
  const tir_t31 = charge_call(re.tir_clone(), cert.tir_clone(), whole.tir_clone(), tir_t30);
  over = tir_t30.v;
  charged = tir_t31;
  if ((charged !== CrOk)) {
    return charged;
  }
  return CrOk;
}

export function cert_install(re, cert, has, pcert, haspike) {
  has.v = false;
  haspike.v = false;
  let shape = CrOk;
  const tir_t1 = cert_shape(re.tir_clone());
  shape = tir_t1;
  if ((shape !== CrOk)) {
    return shape;
  }
  if (re.pike) {
    let tmp1 = false;
    const tir_t2 = pike_price(re.tir_clone(), pcert);
    tmp1 = tir_t2;
    if (tmp1) {
      let tmp2 = CrOk;
      const tir_t3 = cert_check(re.tir_clone(), CfgPike, pcert.v.tir_clone());
      tmp2 = tir_t3;
      if ((tmp2 !== CrOk)) {
        return tmp2;
      }
      haspike.v = true;
    }
  }
  let found = ArShape;
  const tir_t4 = cert_build(re.tir_clone(), cert);
  found = tir_t4;
  if ((found === ArShape)) {
    return CrShape;
  }
  if ((found !== ArOk)) {
    return CrOk;
  }
  let verdict = CrOk;
  const tir_t5 = cert_check(re.tir_clone(), CfgBacktrack, cert.v.tir_clone());
  verdict = tir_t5;
  if ((verdict !== CrOk)) {
    return verdict;
  }
  has.v = true;
  return CrOk;
}

export function cert_shape(re) {
  let code = re.code;
  let regions = re.regions;
  let total = regions.n;
  if ((total === 0)) {
    return CrNoRegions;
  }
  let root = tir_at(regions, 0).tir_clone();
  if ((root.kind !== RkRoot)) {
    return CrRootKind;
  }
  if ((root.parent !== 4294967295)) {
    return CrRootParent;
  }
  if (((root.lo !== 0) || (root.hi !== code.n))) {
    return CrRootRange;
  }
  let ends = new tir_Seq(tir_EMPTY_U32, 0);
  let i = 0;
  while ((i < total)) {
    tir_push(ends, 8208, tir_mk_u32, tir_at(regions, i).lo);
    i = ((i + 1) >>> 0);
  }
  i = 1;
  while ((i < total)) {
    let tmp1 = tir_at(regions, i).tir_clone();
    let tmp2 = tmp1.parent;
    if ((tmp1.kind === RkRoot)) {
      return CrTwoRoots;
    }
    if ((tmp2 >= i)) {
      return CrParentOrder;
    }
    if ((tmp1.lo > tmp1.hi)) {
      return CrBackwards;
    }
    let tmp3 = tir_at(regions, tmp2).tir_clone();
    if (((tmp1.lo < tmp3.lo) || (tmp1.hi > tmp3.hi))) {
      return CrNotNested;
    }
    if ((tmp1.lo < tir_at(ends, tmp2))) {
      return CrOverlap;
    }
    if (((tmp1.kind === RkBranch) && (tmp3.kind !== RkAlt))) {
      return CrChildren;
    }
    const tir_t1 = tmp2;
    tir_bound(ends.n, tir_t1);
    ends.a[tir_t1] = tmp1.hi;
    i = ((i + 1) >>> 0);
  }
  let kids = new tir_Seq(tir_EMPTY_U32, 0);
  let sibs = new tir_Seq(tir_EMPTY_U32, 0);
  const tir_t2 = tir_cell(kids);
  const tir_t3 = tir_cell(sibs);
  region_kids(regions, tir_t2, tir_t3);
  kids = tir_t2.v;
  sibs = tir_t3.v;
  i = 0;
  while ((i < total)) {
    let tmp4 = tir_at(regions, i).tir_clone();
    let tmp5 = tir_at(kids, i);
    let tmp6 = CrShape;
    const tir_t4 = tmp4.kind;
    if (tir_t4 === RkRoot) {
      const tir_t5 = tir_cell(sibs);
      const tir_t6 = shape_span(code, regions, tir_t5, tmp4.lo, tmp4.hi, tmp5);
      sibs = tir_t5.v;
      tmp6 = tir_t6;
    } else if (tir_t4 === RkGroup) {
      const tir_t7 = tir_cell(sibs);
      const tir_t8 = shape_span(code, regions, tir_t7, tmp4.lo, tmp4.hi, tmp5);
      sibs = tir_t7.v;
      tmp6 = tir_t8;
    } else if (tir_t4 === RkBranch) {
      const tir_t9 = tir_cell(sibs);
      const tir_t10 = shape_span(code, regions, tir_t9, tmp4.lo, tmp4.hi, tmp5);
      sibs = tir_t9.v;
      tmp6 = tir_t10;
    } else if (tir_t4 === RkAlt) {
      const tir_t11 = tir_cell(sibs);
      const tir_t12 = shape_alt(code, regions, tir_t11, i, tmp5);
      sibs = tir_t11.v;
      tmp6 = tir_t12;
    } else if (tir_t4 === RkRepeat) {
      const tir_t13 = tir_cell(sibs);
      const tir_t14 = shape_repeat(code, re.reps, regions, tir_t13, i, tmp5);
      sibs = tir_t13.v;
      tmp6 = tir_t14;
    }
    if ((tmp6 !== CrOk)) {
      return tmp6;
    }
    i = ((i + 1) >>> 0);
  }
  return CrOk;
}

export function charge_call(re, cert, whole, over) {
  let novec = tir_cmul(tir_cadd((re.ncap), 1), 2);
  let setup = tir_cmul(tir_cadd((re.nregs), novec), 4);
  let deliver = tir_cmul(novec, 4);
  let reset = tir_cmul((re.nregs), 4);
  let capacity = new Poly();
  let scratch = tir_new_Poly(1, 0, 0, 0, 0, 0);
  let tmp1 = whole.stack.tir_clone();
  capacity = tir_new_Poly(1, 0, 0, 0, 0, 0);
  if ((!(((((tmp1.c0 === 0) && (tmp1.c1 === 0)) && (tmp1.c2 === 0)) && (tmp1.c3 === 0)) && (tmp1.c4 === 0)))) {
    let tmp2 = new Poly();
    const tir_t1 = poly_mul(tmp1.tir_clone(), tir_new_Poly(1, 2, 0, 0, 0, 0), over);
    tmp2 = tir_t1;
    let tmp3 = new Poly();
    const tir_t2 = poly_add(tir_new_Poly(1, 4, 0, 0, 0, 0), tmp2.tir_clone(), over);
    tmp3 = tir_t2;
    capacity = tmp3.tir_clone();
  }
  let tmp4 = new Poly();
  const tir_t3 = poly_mul(capacity.tir_clone(), tir_new_Poly(1, 12, 0, 0, 0, 0), over);
  tmp4 = tir_t3;
  let tmp5 = new Poly();
  const tir_t4 = poly_add(scratch.tir_clone(), tmp4.tir_clone(), over);
  tmp5 = tir_t4;
  scratch = tmp5.tir_clone();
  let tmp6 = whole.trail.tir_clone();
  capacity = tir_new_Poly(1, 0, 0, 0, 0, 0);
  if ((!(((((tmp6.c0 === 0) && (tmp6.c1 === 0)) && (tmp6.c2 === 0)) && (tmp6.c3 === 0)) && (tmp6.c4 === 0)))) {
    let tmp7 = new Poly();
    const tir_t5 = poly_mul(tmp6.tir_clone(), tir_new_Poly(1, 2, 0, 0, 0, 0), over);
    tmp7 = tir_t5;
    let tmp8 = new Poly();
    const tir_t6 = poly_add(tir_new_Poly(1, 4, 0, 0, 0, 0), tmp7.tir_clone(), over);
    tmp8 = tir_t6;
    capacity = tmp8.tir_clone();
  }
  let tmp9 = new Poly();
  const tir_t7 = poly_mul(capacity.tir_clone(), tir_new_Poly(1, 8, 0, 0, 0, 0), over);
  tmp9 = tir_t7;
  let tmp10 = new Poly();
  const tir_t8 = poly_add(scratch.tir_clone(), tmp9.tir_clone(), over);
  tmp10 = tir_t8;
  scratch = tmp10.tir_clone();
  let tmp11 = new Poly();
  const tir_t9 = poly_mul(whole.trail.tir_clone(), tir_new_Poly(1, 4, 0, 0, 0, 0), over);
  tmp11 = tir_t9;
  let tmp12 = new Poly();
  const tir_t10 = poly_add(whole.work.tir_clone(), tmp11.tir_clone(), over);
  tmp12 = tir_t10;
  let tmp13 = new Poly();
  const tir_t11 = poly_add(tir_new_Poly(1, reset, 0, 0, 0, 0), tmp12.tir_clone(), over);
  tmp13 = tir_t11;
  let tmp14 = new Poly();
  const tir_t12 = poly_mul(tmp13.tir_clone(), tir_new_Poly(1, 0, 1, 0, 0, 0), over);
  tmp14 = tir_t12;
  let tmp15 = new Poly();
  const tir_t13 = poly_mul(scratch.tir_clone(), tir_new_Poly(1, 3, 0, 0, 0, 0), over);
  tmp15 = tir_t13;
  let tmp16 = new Poly();
  const tir_t14 = poly_add(tmp14.tir_clone(), tmp15.tir_clone(), over);
  tmp16 = tir_t14;
  let tmp17 = new Poly();
  const tir_t15 = poly_add(tir_new_Poly(1, tir_cadd(setup, deliver), 0, 0, 0, 0), tmp16.tir_clone(), over);
  tmp17 = tir_t15;
  let tmp18 = new Poly();
  const tir_t16 = poly_mul(scratch.tir_clone(), tir_new_Poly(1, 2, 0, 0, 0, 0), over);
  tmp18 = tir_t16;
  let tmp19 = new Poly();
  const tir_t17 = poly_add(tir_new_Poly(1, tir_cadd(setup, deliver), 0, 0, 0, 0), tmp18.tir_clone(), over);
  tmp19 = tir_t17;
  if (over.v) {
    return CrOverflow;
  }
  let holds = false;
  const tir_t18 = poly_ge(cert.cost.tir_clone(), tmp17.tir_clone());
  holds = tir_t18;
  if ((!holds)) {
    return CrTotalCost;
  }
  const tir_t19 = poly_eq(cert.stack.tir_clone(), whole.stack.tir_clone());
  holds = tir_t19;
  if ((!holds)) {
    return CrTotalStack;
  }
  const tir_t20 = poly_eq(cert.trail.tir_clone(), whole.trail.tir_clone());
  holds = tir_t20;
  if ((!holds)) {
    return CrTotalTrail;
  }
  const tir_t21 = poly_ge(cert.mem.tir_clone(), tmp19.tir_clone());
  holds = tir_t21;
  if ((!holds)) {
    return CrTotalMem;
  }
  return CrOk;
}

export function charge_grow(oldcap, lenv, esize, maxv, mem, peak, cost, memlimit, costlimit) {
  if ((lenv < oldcap)) {
    return true;
  }
  if ((lenv >= maxv)) {
    return false;
  }
  let tmp1 = 4;
  let tmp2 = ((Math.imul(oldcap, 2)) >>> 0);
  if ((tmp2 > 4)) {
    tmp1 = tmp2;
  }
  if ((tmp1 > maxv)) {
    tmp1 = maxv;
  }
  let tmp3 = tir_cmul((tmp1), (esize));
  let tmp4 = tir_cmul((oldcap), (esize));
  if ((tmp3 > tir_csub(memlimit, mem.v))) {
    return false;
  }
  let tmp5 = tir_cadd(tmp3, tmp4);
  if ((tmp5 > tir_csub(costlimit, cost.v))) {
    return false;
  }
  cost.v = tir_cadd(cost.v, tmp5);
  let tmp6 = tir_cadd(mem.v, tmp3);
  if ((tmp6 > peak.v)) {
    peak.v = tmp6;
  }
  mem.v = tir_csub(tmp6, tmp4);
  return true;
}

export function check_fit(w, used) {
  let tmp1 = false;
  if ((w.v.fitcode !== (w.v.code.n))) {
    tmp1 = true;
  }
  if ((w.v.fitregion !== (w.v.regions.n))) {
    tmp1 = true;
  }
  if ((w.v.fitrep !== (w.v.nrep))) {
    tmp1 = true;
  }
  if ((w.v.fitvisit !== used)) {
    tmp1 = true;
  }
  if ((w.v.fitjobs !== w.v.peakjobs)) {
    tmp1 = true;
  }
  if ((w.v.fitpatch !== w.v.peakpatch)) {
    tmp1 = true;
  }
  if (tmp1) {
    w.v.err = 1003;
  }
}

export function check_possess(w) {
  let tmp1 = w.v.nodes.n;
  let tmp2 = 0;
  let tmp3 = 0;
  let tmp4 = false;
  let tmp5 = 1;
  while ((tmp5 < tmp1)) {
    let tmp6 = tir_at(w.v.nodes, tmp5).tir_clone();
    const tir_t1 = identity_of(tmp6.kind, tmp6.aux);
    tmp3 = tir_t1;
    if ((tmp3 === 1)) {
      tmp2 = ((tmp2 | 2) >>> 0);
    }
    if ((tmp3 === 2)) {
      tmp2 = ((tmp2 | 4) >>> 0);
    }
    if ((tmp3 === 3)) {
      tmp2 = ((tmp2 | 8) >>> 0);
    }
    if ((tmp3 === 4)) {
      tmp2 = ((tmp2 | 16) >>> 0);
    }
    if ((tmp3 === 5)) {
      tmp2 = ((tmp2 | 32) >>> 0);
    }
    if ((tmp3 === 6)) {
      tmp2 = ((tmp2 | 64) >>> 0);
    }
    if ((tmp3 === 7)) {
      tmp2 = ((tmp2 | 128) >>> 0);
    }
    if ((tmp3 === 8)) {
      tmp2 = ((tmp2 | 256) >>> 0);
    }
    if ((tmp3 === 9)) {
      tmp2 = ((tmp2 | 512) >>> 0);
    }
    if ((tmp3 === 10)) {
      tmp2 = ((tmp2 | 1024) >>> 0);
    }
    if ((tmp3 === 11)) {
      tmp2 = ((tmp2 | 2048) >>> 0);
    }
    if ((tmp3 === 12)) {
      tmp2 = ((tmp2 | 4096) >>> 0);
    }
    if ((tmp3 === 13)) {
      tmp2 = ((tmp2 | 8192) >>> 0);
    }
    if ((tmp6.kind === NdRepeat)) {
      if ((tir_at(w.v.nodes, tmp6.first).kind === NdGroup)) {
        tmp4 = true;
      }
    }
    tmp5 = ((tmp5 + 1) >>> 0);
  }
  let tmp7 = 0;
  tmp5 = ((tmp1 - 1) >>> 0);
  while ((tmp5 > 0)) {
    let tmp8 = tir_at(w.v.nodes, tmp5).tir_clone();
    if (((tmp8.kind === NdRepeat) && (tmp8.aux > tmp8.val))) {
      let tmp9 = tir_at(w.v.nodes, tmp8.first).tir_clone();
      const tir_t2 = identity_of(tmp9.kind, tmp9.aux);
      tmp3 = tir_t2;
      let tmp10 = 0;
      if ((tmp3 === 3)) {
        tmp10 = 10752;
      }
      if ((tmp3 === 7)) {
        tmp10 = 512;
      }
      if ((tmp3 === 9)) {
        tmp10 = 144;
      }
      if ((tmp3 === 11)) {
        tmp10 = 8;
      }
      if ((tmp3 === 13)) {
        tmp10 = 8;
      }
      let tmp11 = tmp7;
      if (tmp4) {
        tmp11 = tmp2;
      }
      if ((((tmp10 & tmp11) >>> 0) !== 0)) {
        w.v.err = 1000;
        w.v.erroff = 0;
        return;
      }
    }
    const tir_t3 = identity_of(tmp8.kind, tmp8.aux);
    tmp3 = tir_t3;
    if ((tmp3 === 1)) {
      tmp7 = ((tmp7 | 2) >>> 0);
    }
    if ((tmp3 === 2)) {
      tmp7 = ((tmp7 | 4) >>> 0);
    }
    if ((tmp3 === 3)) {
      tmp7 = ((tmp7 | 8) >>> 0);
    }
    if ((tmp3 === 4)) {
      tmp7 = ((tmp7 | 16) >>> 0);
    }
    if ((tmp3 === 5)) {
      tmp7 = ((tmp7 | 32) >>> 0);
    }
    if ((tmp3 === 6)) {
      tmp7 = ((tmp7 | 64) >>> 0);
    }
    if ((tmp3 === 7)) {
      tmp7 = ((tmp7 | 128) >>> 0);
    }
    if ((tmp3 === 8)) {
      tmp7 = ((tmp7 | 256) >>> 0);
    }
    if ((tmp3 === 9)) {
      tmp7 = ((tmp7 | 512) >>> 0);
    }
    if ((tmp3 === 10)) {
      tmp7 = ((tmp7 | 1024) >>> 0);
    }
    if ((tmp3 === 11)) {
      tmp7 = ((tmp7 | 2048) >>> 0);
    }
    if ((tmp3 === 12)) {
      tmp7 = ((tmp7 | 4096) >>> 0);
    }
    if ((tmp3 === 13)) {
      tmp7 = ((tmp7 | 8192) >>> 0);
    }
    tmp5 = ((tmp5 - 1) >>> 0);
  }
}

export function class_after_set(w, at, pat) {
  let tmp1 = pat.n;
  let tmp2 = at;
  if ((((tmp2 < tmp1) && (tir_at(pat, tmp2) === 45)) && ((tmp1 > ((tmp2 + 1) >>> 0)) && (tir_at(pat, ((tmp2 + 1) >>> 0)) !== 93)))) {
    w.v.err = 150;
    w.v.erroff = ((tmp2 + 1) >>> 0);
  }
}

export function class_element(w, at, quoting, pat, base, lo, fold) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = base;
  let tmp4 = lo;
  let tmp5 = fold;
  const tir_t1 = tir_cell(tmp2);
  class_skip(pat, tir_t1, quoting);
  tmp2 = tir_t1.v;
  if ((((tmp2 < tmp1) && (tir_at(pat, tmp2) === 45)) && (!quoting.v))) {
    let tmp6 = ((tmp2 + 1) >>> 0);
    let tmp7 = false;
    const tir_t2 = tir_cell(tmp6);
    const tir_t3 = tir_cell(tmp7);
    class_skip(pat, tir_t2, tir_t3);
    tmp6 = tir_t2.v;
    tmp7 = tir_t3.v;
    if (((tmp6 < tmp1) && (tmp7 || (tir_at(pat, tmp6) !== 93)))) {
      let tmp8 = 4294967295;
      if (tmp7) {
        tmp8 = ((tir_at(pat, tmp6)) >>> 0);
        tmp6 = ((tmp6 + 1) >>> 0);
      } else {
        if ((tir_at(pat, tmp6) === 92)) {
          let tmp9 = new Esc();
          const tir_t4 = tir_cell(tmp6);
          const tir_t5 = read_escape(pat, tir_t4, w, true);
          tmp6 = tir_t4.v;
          tmp9 = tir_t5;
          if ((w.v.err !== 0)) {
            return;
          }
          if ((tmp9.kind !== EkChar)) {
            w.v.err = 150;
            w.v.erroff = tmp6;
            return;
          }
          tmp8 = tmp9.val;
        } else {
          if (((tir_at(pat, tmp6) === 91) && (tmp1 > ((tmp6 + 1) >>> 0)))) {
            if ((((tir_at(pat, ((tmp6 + 1) >>> 0)) === 58) || (tir_at(pat, ((tmp6 + 1) >>> 0)) === 46)) || (tir_at(pat, ((tmp6 + 1) >>> 0)) === 61))) {
              let tmp10 = 4294967295;
              const tir_t6 = posix_end(pat, ((tmp6 + 1) >>> 0));
              tmp10 = tir_t6;
              if ((tmp10 !== 4294967295)) {
                w.v.err = 150;
                w.v.erroff = ((tmp10 + 2) >>> 0);
                return;
              }
            }
          }
          tmp8 = ((tir_at(pat, tmp6)) >>> 0);
          tmp6 = ((tmp6 + 1) >>> 0);
        }
      }
      if ((tmp8 < tmp4)) {
        w.v.err = 108;
        w.v.erroff = tmp6;
        return;
      }
      note_element(w, tmp4, tmp8, true);
      set_range(w, tmp3, tmp4, tmp8, tmp5);
      quoting.v = tmp7;
      at.v = tmp6;
      return;
    }
  }
  note_element(w, tmp4, tmp4, false);
  set_range(w, tmp3, tmp4, tmp4, tmp5);
  at.v = tmp2;
}

export function class_from_set(w, which, neg) {
  let tmp1 = 0;
  const tir_t1 = new_class(w);
  tmp1 = tir_t1;
  if ((w.v.err !== 0)) {
    return;
  }
  let tmp2 = ((Math.imul(tmp1, 32)) >>> 0);
  let tmp3 = which;
  let tmp4 = neg;
  set_union(w, tmp2, tmp3, tmp4);
  let tmp5 = 0;
  if (((tmp3 === 0) && (tmp4 === false))) {
    tmp5 = 2;
  }
  if (((tmp3 === 0) && (tmp4 === true))) {
    tmp5 = 1;
  }
  if (((tmp3 === 2) && (tmp4 === false))) {
    tmp5 = 4;
  }
  if (((tmp3 === 2) && (tmp4 === true))) {
    tmp5 = 3;
  }
  if (((tmp3 === 1) && (tmp4 === false))) {
    tmp5 = 6;
  }
  if (((tmp3 === 1) && (tmp4 === true))) {
    tmp5 = 5;
  }
  if (((tmp3 === 3) && (tmp4 === false))) {
    tmp5 = 11;
  }
  if (((tmp3 === 3) && (tmp4 === true))) {
    tmp5 = 10;
  }
  if (((tmp3 === 4) && (tmp4 === false))) {
    tmp5 = 13;
  }
  if (((tmp3 === 4) && (tmp4 === true))) {
    tmp5 = 12;
  }
  attach_atom(w, NdClass, tmp1, tmp5);
}

export function class_has(classes, idx, c) {
  let tmp1 = ((((Math.imul(idx, 32)) >>> 0) + (((c >>> 3)) >>> 0)) >>> 0);
  let tmp2 = tir_at(BITS, ((((c) >>> 0) & 7) >>> 0));
  return (((tir_at(classes, tmp1) & tmp2) & 255) !== 0);
}

export function class_skip(pat, at, quoting) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  while ((tmp1 > ((tmp2 + 1) >>> 0))) {
    if ((tir_at(pat, tmp2) !== 92)) {
      break;
    }
    let tmp3 = tir_at(pat, ((tmp2 + 1) >>> 0));
    if ((tmp3 === 81)) {
      quoting.v = true;
      tmp2 = ((tmp2 + 2) >>> 0);
      continue;
    }
    if ((tmp3 === 69)) {
      quoting.v = false;
      tmp2 = ((tmp2 + 2) >>> 0);
      continue;
    }
    break;
  }
  at.v = tmp2;
}

export function close_group(w) {
  let tmp1 = new Frame();
  tmp1 = tir_pop(w.v.frames);
  w.v.opts = tmp1.opts;
  if ((tmp1.unsup !== 0)) {
    w.v.err = 1000;
    w.v.erroff = tmp1.unsup;
    return;
  }
  let tmp2 = ((w.v.frames.n - 1) >>> 0);
  const tir_t1 = tmp2;
  tir_bound(w.v.frames.n, tir_t1);
  w.v.frames.a[tir_t1].qual = tmp1.grp;
}

export function close_region(w, at) {
  let tmp1 = at;
  if ((tmp1 >= w.v.regions.n)) {
    return;
  }
  const tir_t1 = tmp1;
  tir_bound(w.v.regions.n, tir_t1);
  w.v.regions.a[tir_t1].hi = w.v.code.n;
}

export function compile(pat, popts, nltype, bsr, out) {
  out.v.err = 0;
  out.v.erroff = 0;
  let tmp1 = pat.n;
  if ((tmp1 > 4096)) {
    out.v.err = 1002;
    return;
  }
  let w = new Work();
  const tir_t1 = tir_cell(w);
  parse(pat, popts, nltype, tir_t1);
  w = tir_t1.v;
  if ((w.err !== 0)) {
    out.v.err = w.err;
    out.v.erroff = w.erroff;
    return;
  }
  let tmp2 = (((popts & 64) >>> 0) !== 0);
  const tir_t2 = tir_cell(w);
  generate(tir_t2, tmp2);
  w = tir_t2.v;
  if ((w.err !== 0)) {
    out.v.err = w.err;
    out.v.erroff = w.erroff;
    return;
  }
  let tmp3 = ((((Math.imul(((w.ncap + 1) >>> 0), 2)) >>> 0) + ((Math.imul(w.nrep, 2)) >>> 0)) >>> 0);
  if ((tmp3 > 8704)) {
    out.v.err = 1002;
    return;
  }
  out.v.re.ncap = w.ncap;
  out.v.re.nname = w.nname;
  out.v.re.nregs = tmp3;
  out.v.re.opts = popts;
  out.v.re.nltype = nltype;
  out.v.re.bsr = bsr;
  out.v.re.hascrlf = w.hascrlf;
  out.v.re.crfirst = w.crfirst;
  out.v.re.lowdec = w.lowdec;
  out.v.re.blockers = w.blockers;
  out.v.re.lowfits = w.lowfits;
  out.v.re.code = w.code;
  w.code = new tir_Seq(tir_EMPTY_OBJ, 0);
  out.v.re.classes = w.classes;
  w.classes = new tir_Seq(tir_EMPTY_U8, 0);
  out.v.re.reps = w.reps;
  w.reps = new tir_Seq(tir_EMPTY_OBJ, 0);
  out.v.re.regions = w.regions;
  w.regions = new tir_Seq(tir_EMPTY_OBJ, 0);
  out.v.re.names = w.names;
  w.names = new tir_Seq(tir_EMPTY_U8, 0);
  out.v.re.nameents = w.nameents;
  w.nameents = new tir_Seq(tir_EMPTY_OBJ, 0);
  let tmp4 = false;
  const tir_t3 = pike_ok(out.v.re.tir_clone());
  tmp4 = tir_t3;
  out.v.re.pike = tmp4;
  let cand = new Cert();
  let tmp5 = false;
  let pcand = new Cert();
  let tmp6 = false;
  let tmp7 = CrOk;
  const tir_t4 = tir_cell(cand);
  const tir_t5 = tir_cell(tmp5);
  const tir_t6 = tir_cell(pcand);
  const tir_t7 = tir_cell(tmp6);
  const tir_t8 = cert_install(out.v.re.tir_clone(), tir_t4, tir_t5, tir_t6, tir_t7);
  cand = tir_t4.v;
  tmp5 = tir_t5.v;
  pcand = tir_t6.v;
  tmp6 = tir_t7.v;
  tmp7 = tir_t8;
  if ((tmp7 !== CrOk)) {
    out.v.err = 1003;
    return;
  }
  out.v.re.cert = cand.tir_clone();
  out.v.re.hascert = tmp5;
  out.v.re.pikecert = pcand.tir_clone();
  out.v.re.haspikecert = tmp6;
}

export function ct(c, bit) {
  return (((tir_at(CTYPE, ((c) >>> 0)) & bit) & 255) !== 0);
}

export function ctx_create(re, mcfg, maxlen, costlimit, stacklimit, memlimit, ctx) {
  ctx.v.ready = false;
  let answered = new Answer();
  const tir_t1 = re_mem(re.tir_clone(), mcfg, (maxlen));
  answered = tir_t1;
  if ((answered.status !== 0)) {
    return answered.status;
  }
  let resident = answered.value;
  let picked = new Cert();
  let has = false;
  const tir_t2 = tir_cell(picked);
  const tir_t3 = re_pick(re.tir_clone(), tir_t2);
  picked = tir_t2.v;
  has = tir_t3;
  if ((!has)) {
    return 4;
  }
  let over = false;
  let novec = ((Math.imul(((re.ncap + 1) >>> 0), 2)) >>> 0);
  let answer = tir_cmul((novec), 4);
  let setup = 0;
  let ballast = 0;
  let nregs = 0;
  let cbt = 0;
  let ctrail = 0;
  let clists = 0;
  let cstk = 0;
  let ctab = 0;
  let cpool = 0;
  let words = 0;
  if (re.pike) {
    let room = new Room();
    const tir_t4 = tir_cell(room);
    const tir_t5 = tir_cell(over);
    pike_room(re.tir_clone(), tir_t4, tir_t5);
    room = tir_t4.v;
    over = tir_t5.v;
    words = room.words;
    clists = room.lists;
    cstk = room.stk;
    ctab = room.tables;
    cpool = room.pool;
    ballast = room.reserved;
    setup = tir_cadd(tir_cmul((novec), 4), (words));
  } else {
    let tmp1 = new Bound();
    const tir_t6 = poly_value(picked.stack.tir_clone(), (maxlen));
    tmp1 = tir_t6;
    let tmp2 = new Bound();
    const tir_t7 = poly_value(picked.trail.tir_clone(), (maxlen));
    tmp2 = tir_t7;
    if ((!tmp1.ok)) {
      return 4;
    }
    if ((!tmp2.ok)) {
      return 4;
    }
    let tmp3 = 0;
    if ((tmp1.value > 0)) {
      let tmp4 = 0;
      const tir_t8 = tir_cell(over);
      const tir_t9 = sat_mul(tmp1.value, 2, tir_t8);
      over = tir_t8.v;
      tmp4 = tir_t9;
      let tmp5 = 0;
      const tir_t10 = tir_cell(over);
      const tir_t11 = sat_add(tmp4, 4, tir_t10);
      over = tir_t10.v;
      tmp5 = tir_t11;
      tmp3 = tmp5;
    }
    cbt = tmp3;
    let tmp6 = 0;
    if ((tmp2.value > 0)) {
      let tmp7 = 0;
      const tir_t12 = tir_cell(over);
      const tir_t13 = sat_mul(tmp2.value, 2, tir_t12);
      over = tir_t12.v;
      tmp7 = tir_t13;
      let tmp8 = 0;
      const tir_t14 = tir_cell(over);
      const tir_t15 = sat_add(tmp7, 4, tir_t14);
      over = tir_t14.v;
      tmp8 = tir_t15;
      tmp6 = tmp8;
    }
    ctrail = tmp6;
    let tmp9 = 0;
    const tir_t16 = tir_cell(over);
    const tir_t17 = sat_mul(cbt, 12, tir_t16);
    over = tir_t16.v;
    tmp9 = tir_t17;
    let tmp10 = 0;
    const tir_t18 = tir_cell(over);
    const tir_t19 = sat_mul(ctrail, 8, tir_t18);
    over = tir_t18.v;
    tmp10 = tir_t19;
    let tmp11 = 0;
    const tir_t20 = tir_cell(over);
    const tir_t21 = sat_add(tmp9, tmp10, tir_t20);
    over = tir_t20.v;
    tmp11 = tir_t21;
    tmp9 = tmp11;
    ballast = tmp9;
    nregs = re.nregs;
    setup = tir_cmul((((nregs + novec) >>> 0)), 4);
  }
  let tmp12 = 0;
  const tir_t22 = tir_cell(over);
  const tir_t23 = sat_add(setup, answer, tir_t22);
  over = tir_t22.v;
  tmp12 = tir_t23;
  let tmp13 = 0;
  const tir_t24 = tir_cell(over);
  const tir_t25 = sat_add(tmp12, ballast, tir_t24);
  over = tir_t24.v;
  tmp13 = tir_t25;
  let tmp14 = tmp13;
  if (over) {
    return 4;
  }
  if ((tmp14 > resident)) {
    return 4;
  }
  if ((resident > memlimit)) {
    return 2;
  }
  if ((resident > costlimit)) {
    return 2;
  }
  let blank = new Ctx();
  const tir_t26 = ctx.v;
  ctx.v = blank;
  blank = tir_t26;
  tir_reserve(ctx.v.regs, nregs, 8704, tir_mk_u32);
  tir_reserve(ctx.v.bt, ((cbt) >>> 0), 178956970, tir_mk_obj);
  tir_reserve(ctx.v.trail, ((ctrail) >>> 0), 268435455, tir_mk_obj);
  tir_reserve(ctx.v.clist, ((clists) >>> 0), 65700, tir_mk_obj);
  tir_reserve(ctx.v.nlist, ((clists) >>> 0), 65700, tir_mk_obj);
  tir_reserve(ctx.v.stk, ((cstk) >>> 0), 131396, tir_mk_obj);
  tir_reserve(ctx.v.seen, words, 2147483647, tir_mk_u8);
  tir_reserve(ctx.v.rc, ((ctab) >>> 0), 262796, tir_mk_u32);
  tir_reserve(ctx.v.free, ((ctab) >>> 0), 262796, tir_mk_u32);
  tir_reserve(ctx.v.pool, ((cpool) >>> 0), 134549508, tir_mk_u32);
  tir_reserve(ctx.v.slack, ((tir_csub(resident, tmp14)) >>> 0), 2147483647, tir_mk_u8);
  ctx.v.re = re.tir_clone();
  ctx.v.maxlen = maxlen;
  ctx.v.costcap = costlimit;
  ctx.v.stackcap = stacklimit;
  ctx.v.memcap = resident;
  ctx.v.ready = true;
  return 0;
}

export function ctx_match(ctx, subj, start, mopts, costlimit, stacklimit, ov, use) {
  use.v.cost = 0;
  use.v.stack = 0;
  use.v.mem = 0;
  if ((!ctx.v.ready)) {
    return 3;
  }
  if ((ctx.v.maxlen < subj.n)) {
    return 3;
  }
  if ((costlimit > ctx.v.costcap)) {
    return 3;
  }
  if ((stacklimit > ctx.v.stackcap)) {
    return 3;
  }
  let tmp1 = 1;
  if (ctx.v.re.pike) {
    const tir_t1 = tir_cell(ctx.v.clist);
    const tir_t2 = tir_cell(ctx.v.nlist);
    const tir_t3 = tir_cell(ctx.v.stk);
    const tir_t4 = tir_cell(ctx.v.seen);
    const tir_t5 = tir_cell(ctx.v.pool);
    const tir_t6 = tir_cell(ctx.v.rc);
    const tir_t7 = tir_cell(ctx.v.free);
    const tir_t8 = pike_run(ctx.v.re.tir_clone(), subj, start, mopts, costlimit, stacklimit, ctx.v.memcap, tir_t1, tir_t2, tir_t3, tir_t4, tir_t5, tir_t6, tir_t7, ov, use);
    ctx.v.clist = tir_t1.v;
    ctx.v.nlist = tir_t2.v;
    ctx.v.stk = tir_t3.v;
    ctx.v.seen = tir_t4.v;
    ctx.v.pool = tir_t5.v;
    ctx.v.rc = tir_t6.v;
    ctx.v.free = tir_t7.v;
    tmp1 = tir_t8;
  } else {
    const tir_t9 = tir_cell(ctx.v.regs);
    const tir_t10 = tir_cell(ctx.v.bt);
    const tir_t11 = tir_cell(ctx.v.trail);
    const tir_t12 = bt_run(ctx.v.re.tir_clone(), subj, start, mopts, costlimit, stacklimit, ctx.v.memcap, tir_t9, tir_t10, tir_t11, ov, use);
    ctx.v.regs = tir_t9.v;
    ctx.v.bt = tir_t10.v;
    ctx.v.trail = tir_t11.v;
    tmp1 = tir_t12;
  }
  use.v.mem = ctx.v.memcap;
  return tmp1;
}

export function drop_empty_region(w, at) {
  let tmp1 = at;
  if ((tmp1 >= w.v.regions.n)) {
    return;
  }
  if ((tir_at(w.v.regions, tmp1).lo === w.v.code.n)) {
    tir_truncate(w.v.regions, tmp1);
  }
}

export function emit(w, op, arg, alt) {
  let tmp1 = w.v.code.n;
  if ((tmp1 >= 32848)) {
    w.v.err = 1002;
    return 0;
  }
  tir_push(w.v.code, 32848, tir_mk_obj, tir_new_Inst(op, arg, alt));
  return tmp1;
}

export function generate(w, endanchored) {
  plan_lowering(w, endanchored);
  if ((w.v.err !== 0)) {
    return;
  }
  let tmp1 = w.v.root;
  let tmp2 = 0;
  const tir_t1 = open_region(w, RkRoot, 4294967295);
  tmp2 = tir_t1;
  push_job(w, tmp1, tmp2);
  let tmp3 = 65664;
  let tmp4 = 0;
  while ((((w.v.jobs.n > 0) && (tmp3 > 0)) && (w.v.err === 0))) {
    tmp3 = tir_csub(tmp3, 1);
    let tmp5 = ((w.v.jobs.n - 1) >>> 0);
    let tmp6 = tir_at(w.v.jobs, tmp5).tir_clone();
    let tmp7 = tir_at(w.v.nodes, tmp6.node).tir_clone();
    let tmp8 = new Job();
    const tir_t2 = tmp7.kind;
    if (tir_t2 === NdNil) {
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdChar) {
      const tir_t3 = emit(w, OpChar, tmp7.val, 0);
      tmp4 = tir_t3;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdCharCI) {
      const tir_t4 = emit(w, OpCharCI, tmp7.val, 0);
      tmp4 = tir_t4;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdClass) {
      const tir_t5 = emit(w, OpClass, tmp7.val, 0);
      tmp4 = tir_t5;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdAny) {
      const tir_t6 = emit(w, OpAny, tmp7.val, 0);
      tmp4 = tir_t6;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdAnyNoNL) {
      const tir_t7 = emit(w, OpAnyNoNL, tmp7.val, 0);
      tmp4 = tir_t7;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdBsr) {
      const tir_t8 = emit(w, OpBsr, tmp7.val, 0);
      tmp4 = tir_t8;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdCirc) {
      const tir_t9 = emit(w, OpCirc, tmp7.val, 0);
      tmp4 = tir_t9;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdCircM) {
      const tir_t10 = emit(w, OpCircM, tmp7.val, 0);
      tmp4 = tir_t10;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdDoll) {
      const tir_t11 = emit(w, OpDoll, tmp7.val, 0);
      tmp4 = tir_t11;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdDollE) {
      const tir_t12 = emit(w, OpDollE, tmp7.val, 0);
      tmp4 = tir_t12;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdDollM) {
      const tir_t13 = emit(w, OpDollM, tmp7.val, 0);
      tmp4 = tir_t13;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdSod) {
      const tir_t14 = emit(w, OpSod, tmp7.val, 0);
      tmp4 = tir_t14;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdEod) {
      const tir_t15 = emit(w, OpEod, tmp7.val, 0);
      tmp4 = tir_t15;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdEodn) {
      const tir_t16 = emit(w, OpEodn, tmp7.val, 0);
      tmp4 = tir_t16;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdWordB) {
      const tir_t17 = emit(w, OpWordB, tmp7.val, 0);
      tmp4 = tir_t17;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdNotWordB) {
      const tir_t18 = emit(w, OpNotWordB, tmp7.val, 0);
      tmp4 = tir_t18;
      tmp8 = tir_pop(w.v.jobs);
    } else if (tir_t2 === NdConcat) {
      let tmp9 = tmp7.first;
      if ((tmp6.phase !== 0)) {
        tmp9 = tir_at(w.v.nodes, tmp6.cur).nxt;
      }
      if ((tmp9 === 0)) {
        tmp8 = tir_pop(w.v.jobs);
      } else {
        const tir_t19 = tmp5;
        tir_bound(w.v.jobs.n, tir_t19);
        w.v.jobs.a[tir_t19].phase = 1;
        const tir_t20 = tmp5;
        tir_bound(w.v.jobs.n, tir_t20);
        w.v.jobs.a[tir_t20].cur = tmp9;
        push_job(w, tmp9, tmp6.here);
      }
    } else if (tir_t2 === NdGroup) {
      if ((tmp6.phase === 0)) {
        let tmp10 = 0;
        const tir_t21 = open_region(w, RkGroup, tmp6.here);
        tmp10 = tir_t21;
        const tir_t22 = tmp5;
        tir_bound(w.v.jobs.n, tir_t22);
        w.v.jobs.a[tir_t22].here = tmp10;
        if ((tmp7.val !== 0)) {
          let tmp11 = ((Math.imul(tmp7.val, 2)) >>> 0);
          const tir_t23 = emit(w, OpSave, tmp11, 0);
          tmp4 = tir_t23;
        }
        const tir_t24 = tmp5;
        tir_bound(w.v.jobs.n, tir_t24);
        w.v.jobs.a[tir_t24].phase = 1;
        let tmp12 = tmp7.first;
        if ((tmp12 !== 0)) {
          push_job(w, tmp12, tmp10);
        }
      } else {
        if ((tmp7.val !== 0)) {
          let tmp13 = ((((Math.imul(tmp7.val, 2)) >>> 0) + 1) >>> 0);
          const tir_t25 = emit(w, OpSave, tmp13, 0);
          tmp4 = tir_t25;
        }
        close_region(w, tmp6.here);
        drop_empty_region(w, tmp6.here);
        tmp8 = tir_pop(w.v.jobs);
      }
    } else if (tir_t2 === NdAlt) {
      walk_alt(w, tmp5, tmp6.tir_clone(), tmp7.tir_clone());
    } else if (tir_t2 === NdRepeat) {
      walk_repeat(w, tmp5, tmp6.tir_clone(), tmp7.tir_clone());
    }
  }
  if ((w.v.err !== 0)) {
    return;
  }
  if ((tmp3 === 0)) {
    w.v.err = 1003;
    return;
  }
  if (endanchored) {
    const tir_t26 = emit(w, OpEod, 0, 0);
    tmp4 = tir_t26;
  }
  const tir_t27 = emit(w, OpAccept, 0, 0);
  tmp4 = tir_t27;
  close_region(w, tmp2);
  if (((w.v.err === 0) && w.v.predicted)) {
    check_fit(w, tir_csub(65664, tmp3));
  }
  if ((w.v.err === 0)) {
    scan_first(w);
  }
}

export function hex_value(c) {
  if ((c <= 57)) {
    return ((((c - 48) & 255)) >>> 0);
  }
  return ((((((((c | 32) & 255) - 97) & 255) + 10) & 255)) >>> 0);
}

export function identity_of(kind, aux) {
  const tir_t1 = kind;
  if (tir_t1 === NdClass) {
    return aux;
  } else if (tir_t1 === NdAnyNoNL) {
    return 7;
  } else if (tir_t1 === NdAny) {
    return 8;
  } else if (tir_t1 === NdBsr) {
    return 9;
  } else {
    return 0;
  }
}

export function mark_seen(w, pc) {
  let tmp1 = pc;
  if ((tmp1 >= w.v.code.n)) {
    return;
  }
  let tmp2 = (tmp1 >>> 3);
  let tmp3 = tir_at(BITS, ((tmp1 & 7) >>> 0));
  if ((((tir_at(w.v.seen, tmp2) & tmp3) & 255) !== 0)) {
    return;
  }
  const tir_t1 = tmp2;
  tir_bound(w.v.seen.n, tir_t1);
  w.v.seen.a[tir_t1] = ((tir_at(w.v.seen, tmp2) | tmp3) & 255);
  tir_push(w.v.pending, 32848, tir_mk_u32, tmp1);
}

export function match(re, subj, start, mopts, mcfg, costlimit, stacklimit, memlimit, ov, use) {
  use.v.cost = 0;
  use.v.stack = 0;
  use.v.mem = 0;
  if ((mcfg !== 0)) {
    return 3;
  }
  let tmp1 = 1;
  if (re.pike) {
    const tir_t1 = pike_match(re.tir_clone(), subj, start, mopts, costlimit, stacklimit, memlimit, ov, use);
    tmp1 = tir_t1;
    return tmp1;
  }
  const tir_t2 = bt_match(re.tir_clone(), subj, start, mopts, costlimit, stacklimit, memlimit, ov, use);
  tmp1 = tir_t2;
  return tmp1;
}

export function name_taken(pat, off, nlen, w) {
  let tmp1 = 0;
  let tmp2 = w.v.nameents.n;
  while ((tmp1 < tmp2)) {
    let tmp3 = tir_at(w.v.nameents, tmp1).tir_clone();
    if ((tmp3.nlen === nlen)) {
      let tmp4 = 0;
      let tmp5 = true;
      while ((tmp4 < nlen)) {
        if ((tir_at(w.v.names, ((tmp3.off + tmp4) >>> 0)) !== tir_at(pat, ((off + tmp4) >>> 0)))) {
          tmp5 = false;
          break;
        }
        tmp4 = ((tmp4 + 1) >>> 0);
      }
      if (tmp5) {
        return true;
      }
    }
    tmp1 = ((tmp1 + 1) >>> 0);
  }
  return false;
}

export function named_group(pat, at, w, start, term, here) {
  let tmp1 = pat.n;
  let tmp2 = start;
  let tmp3 = false;
  if ((tmp2 < tmp1)) {
    const tir_t1 = ct(tir_at(pat, tmp2), 4);
    tmp3 = tir_t1;
  }
  if (tmp3) {
    w.v.err = 144;
    w.v.erroff = ((tmp2 + 1) >>> 0);
    return;
  }
  let tmp4 = tmp2;
  let tmp5 = false;
  while ((tmp4 < tmp1)) {
    const tir_t2 = ct(tir_at(pat, tmp4), 1);
    tmp5 = tir_t2;
    if ((!tmp5)) {
      break;
    }
    tmp4 = ((tmp4 + 1) >>> 0);
  }
  let tmp6 = ((tmp4 - tmp2) >>> 0);
  if ((tmp6 === 0)) {
    w.v.err = 162;
    w.v.erroff = tmp2;
    return;
  }
  if ((tmp6 > 128)) {
    w.v.err = 148;
    w.v.erroff = tmp4;
    return;
  }
  if (((tmp4 >= tmp1) || (tir_at(pat, tmp4) !== term))) {
    w.v.err = 142;
    w.v.erroff = tmp4;
    return;
  }
  let tmp7 = false;
  const tir_t3 = name_taken(pat, tmp2, tmp6, w);
  tmp7 = tir_t3;
  if (tmp7) {
    w.v.err = 143;
    w.v.erroff = ((tmp4 + 1) >>> 0);
    return;
  }
  if (((w.v.ncap >= 255) || ((w.v.nname >= 255) || (((w.v.names.n + tmp6) >>> 0) > 4096)))) {
    w.v.err = 1002;
    return;
  }
  let tmp8 = ((w.v.ncap + 1) >>> 0);
  w.v.ncap = tmp8;
  let tmp9 = w.v.names.n;
  tir_push(w.v.nameents, 255, tir_mk_obj, tir_new_NameEnt(tmp9, tmp6, tmp8));
  w.v.nname = ((w.v.nname + 1) >>> 0);
  let tmp10 = 0;
  while ((tmp10 < tmp6)) {
    let tmp11 = tir_at(pat, ((tmp2 + tmp10) >>> 0));
    tir_push(w.v.names, 2147483647, tir_mk_u8, tmp11);
    tmp10 = ((tmp10 + 1) >>> 0);
  }
  let tmp12 = w.v.opts;
  let tmp13 = here;
  push_frame(w, tmp8, tmp12, tmp13, 0);
  at.v = ((tmp4 + 1) >>> 0);
}

export function new_branch(w) {
  let tmp1 = ((w.v.frames.n - 1) >>> 0);
  let tmp2 = tir_at(w.v.frames, tmp1).alt;
  if ((tmp2 === 0)) {
    let tmp3 = 0;
    const tir_t1 = alloc_node(w, NdAlt, 0, 0, 0);
    tmp3 = tir_t1;
    if ((w.v.err !== 0)) {
      return;
    }
    let tmp4 = tir_at(w.v.frames, tmp1).grp;
    let tmp5 = tir_at(w.v.nodes, tmp4).first;
    const tir_t2 = tmp3;
    tir_bound(w.v.nodes.n, tir_t2);
    w.v.nodes.a[tir_t2].first = tmp5;
    const tir_t3 = tmp3;
    tir_bound(w.v.nodes.n, tir_t3);
    w.v.nodes.a[tir_t3].last = tmp5;
    const tir_t4 = tmp4;
    tir_bound(w.v.nodes.n, tir_t4);
    w.v.nodes.a[tir_t4].first = tmp3;
    const tir_t5 = tmp4;
    tir_bound(w.v.nodes.n, tir_t5);
    w.v.nodes.a[tir_t5].last = tmp3;
    const tir_t6 = tmp1;
    tir_bound(w.v.frames.n, tir_t6);
    w.v.frames.a[tir_t6].alt = tmp3;
    tmp2 = tmp3;
  }
  let tmp6 = 0;
  const tir_t7 = alloc_node(w, NdConcat, 0, 0, 0);
  tmp6 = tir_t7;
  if ((w.v.err !== 0)) {
    return;
  }
  add_child(w, tmp2, tmp6);
  const tir_t8 = tmp1;
  tir_bound(w.v.frames.n, tir_t8);
  w.v.frames.a[tir_t8].cat = tmp6;
  const tir_t9 = tmp1;
  tir_bound(w.v.frames.n, tir_t9);
  w.v.frames.a[tir_t9].qual = 0;
}

export function new_class(w) {
  if ((w.v.nclass >= 4096)) {
    w.v.err = 1002;
    return 0;
  }
  let tmp1 = 0;
  while ((tmp1 < 32)) {
    tir_push(w.v.classes, 2147483647, tir_mk_u8, 0);
    tmp1 = ((tmp1 + 1) >>> 0);
  }
  let tmp2 = w.v.nclass;
  w.v.nclass = ((tmp2 + 1) >>> 0);
  return tmp2;
}

export function new_rep(w) {
  let tmp1 = w.v.nrep;
  if ((tmp1 >= 4096)) {
    w.v.err = 1002;
    return 0;
  }
  tir_push(w.v.reps, 4096, tir_mk_obj, tir_new_Rep(0, 0, true, 0, 0, 0));
  w.v.nrep = ((tmp1 + 1) >>> 0);
  return tmp1;
}

export function newline_at(subj, pos, nltype) {
  let tmp1 = subj.n;
  if ((pos >= tmp1)) {
    return 0;
  }
  let tmp2 = tir_at(subj, pos);
  if ((nltype === 0)) {
    if ((tmp2 === 10)) {
      return 1;
    }
    return 0;
  }
  if ((nltype === 1)) {
    if ((tmp2 === 13)) {
      return 1;
    }
    return 0;
  }
  if ((nltype === 2)) {
    if (((tmp2 === 13) && ((tmp1 > ((pos + 1) >>> 0)) && (tir_at(subj, ((pos + 1) >>> 0)) === 10)))) {
      return 2;
    }
    return 0;
  }
  if ((tmp2 === 10)) {
    return 1;
  }
  if ((tmp2 === 13)) {
    if (((tmp1 > ((pos + 1) >>> 0)) && (tir_at(subj, ((pos + 1) >>> 0)) === 10))) {
      return 2;
    }
    return 1;
  }
  if ((nltype === 4)) {
    if (((tmp2 === 11) || ((tmp2 === 12) || (tmp2 === 133)))) {
      return 1;
    }
  }
  return 0;
}

export function newline_before(subj, pos, nltype) {
  if ((pos === 0)) {
    return 0;
  }
  if ((nltype === 0)) {
    if ((tir_at(subj, ((pos - 1) >>> 0)) === 10)) {
      return 1;
    }
    return 0;
  }
  if ((nltype === 1)) {
    if ((tir_at(subj, ((pos - 1) >>> 0)) === 13)) {
      return 1;
    }
    return 0;
  }
  if ((nltype === 2)) {
    if (((pos >= 2) && ((tir_at(subj, ((pos - 2) >>> 0)) === 13) && (tir_at(subj, ((pos - 1) >>> 0)) === 10)))) {
      return 2;
    }
    return 0;
  }
  let tmp1 = tir_at(subj, ((pos - 1) >>> 0));
  if ((tmp1 === 10)) {
    if (((pos >= 2) && (tir_at(subj, ((pos - 2) >>> 0)) === 13))) {
      return 2;
    }
    return 1;
  }
  if ((tmp1 === 13)) {
    return 1;
  }
  if ((nltype === 4)) {
    if (((tmp1 === 11) || ((tmp1 === 12) || (tmp1 === 133)))) {
      return 1;
    }
  }
  return 0;
}

export function note_element(w, lo, hi, ranged) {
  if ((ranged && (lo !== hi))) {
    w.v.clsrange = 1;
  } else {
    w.v.clselems = ((w.v.clselems + 1) >>> 0);
  }
  if ((((((lo) & 255) === 13) || (((lo) & 255) === 10)) || ((((hi) & 255) === 13) || (((hi) & 255) === 10)))) {
    w.v.clscrlf = 1;
  }
}

export function note_ref(w, num, off, nlen) {
  if ((w.v.refs.n >= 2048)) {
    w.v.err = 1002;
    return;
  }
  tir_push(w.v.refs, 2048, tir_mk_obj, tir_new_Ref(num, off, nlen));
}

export function open_group(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = ((at.v + 1) >>> 0);
  let tmp3 = at.v;
  if ((((tmp2 < tmp1) && (tir_at(pat, tmp2) === 42)) && ((tmp1 > ((tmp2 + 1) >>> 0)) && (tir_at(pat, ((tmp2 + 1) >>> 0)) !== 41)))) {
    w.v.err = 1000;
    w.v.erroff = ((tmp2 + 1) >>> 0);
    return;
  }
  if (((tmp2 >= tmp1) || (tir_at(pat, tmp2) !== 63))) {
    if ((w.v.ncap >= 255)) {
      w.v.err = 1002;
      return;
    }
    let tmp4 = ((w.v.ncap + 1) >>> 0);
    w.v.ncap = tmp4;
    let tmp5 = w.v.opts;
    push_frame(w, tmp4, tmp5, tmp3, 0);
    at.v = tmp2;
    return;
  }
  let tmp6 = ((tmp2 + 1) >>> 0);
  if ((tmp6 >= tmp1)) {
    w.v.err = 114;
    w.v.erroff = tmp1;
    return;
  }
  let tmp7 = tir_at(pat, tmp6);
  if ((tmp7 === 35)) {
    let tmp8 = ((tmp6 + 1) >>> 0);
    while (((tmp8 < tmp1) && (tir_at(pat, tmp8) !== 41))) {
      tmp8 = ((tmp8 + 1) >>> 0);
    }
    if ((tmp8 >= tmp1)) {
      w.v.err = 118;
      w.v.erroff = tmp1;
      return;
    }
    at.v = ((tmp8 + 1) >>> 0);
    return;
  }
  if ((tmp7 === 58)) {
    let tmp9 = w.v.opts;
    push_frame(w, 0, tmp9, tmp3, 0);
    at.v = ((tmp6 + 1) >>> 0);
    return;
  }
  let tmp10 = 0;
  if ((((((tmp7 === 61) || (tmp7 === 33)) || (tmp7 === 62)) || (tmp7 === 124)) || (tmp7 === 42))) {
    tmp10 = ((tmp6 + 1) >>> 0);
  }
  if (((tmp7 === 60) && ((tmp1 > ((tmp6 + 1) >>> 0)) && (((tir_at(pat, ((tmp6 + 1) >>> 0)) === 61) || (tir_at(pat, ((tmp6 + 1) >>> 0)) === 33)) || (tir_at(pat, ((tmp6 + 1) >>> 0)) === 42))))) {
    tmp10 = ((tmp6 + 2) >>> 0);
  }
  if ((tmp10 !== 0)) {
    let tmp11 = w.v.opts;
    push_frame(w, 0, tmp11, tmp3, tmp10);
    at.v = tmp10;
    return;
  }
  let tmp12 = false;
  let tmp13 = 62;
  let tmp14 = 0;
  if ((tmp7 === 60)) {
    tmp12 = true;
    tmp14 = ((tmp6 + 1) >>> 0);
  }
  if ((tmp7 === 39)) {
    tmp12 = true;
    tmp13 = 39;
    tmp14 = ((tmp6 + 1) >>> 0);
  }
  if (((tmp7 === 80) && ((tmp1 > ((tmp6 + 1) >>> 0)) && (tir_at(pat, ((tmp6 + 1) >>> 0)) === 60)))) {
    tmp12 = true;
    tmp14 = ((tmp6 + 2) >>> 0);
  }
  if (tmp12) {
    named_group(pat, at, w, tmp14, tmp13, tmp3);
    return;
  }
  if ((((((((tmp7 === 38) || (tmp7 === 43)) || (tmp7 === 82)) || (tmp7 === 80)) || (tmp7 === 67)) || (tmp7 === 40)) || (tmp7 === 91))) {
    w.v.err = 1000;
    w.v.erroff = ((tmp6 + 1) >>> 0);
    return;
  }
  let tmp15 = false;
  const tir_t1 = ct(tmp7, 4);
  tmp15 = tir_t1;
  if (((tmp7 === 45) && (tmp1 > ((tmp6 + 1) >>> 0)))) {
    const tir_t2 = ct(tir_at(pat, ((tmp6 + 1) >>> 0)), 4);
    tmp15 = tir_t2;
    if (tmp15) {
      w.v.err = 1000;
      w.v.erroff = ((tmp6 + 2) >>> 0);
      return;
    }
    tmp15 = false;
  }
  if (tmp15) {
    w.v.err = 1000;
    w.v.erroff = ((tmp6 + 1) >>> 0);
    return;
  }
  let tmp16 = 0;
  let tmp17 = 0;
  let tmp18 = false;
  let tmp19 = true;
  let tmp20 = false;
  let tmp21 = false;
  let tmp22 = tmp6;
  while ((tmp22 < tmp1)) {
    let tmp23 = tir_at(pat, tmp22);
    if ((tmp23 === 45)) {
      if ((tmp18 || tmp21)) {
        w.v.err = 194;
        w.v.erroff = ((tmp22 + 1) >>> 0);
        return;
      }
      tmp18 = true;
      tmp22 = ((tmp22 + 1) >>> 0);
      continue;
    }
    let tmp24 = 0;
    if ((tmp23 === 105)) {
      tmp24 = 1;
    }
    if ((tmp23 === 109)) {
      tmp24 = 2;
    }
    if ((tmp23 === 115)) {
      tmp24 = 4;
    }
    if ((tmp23 === 120)) {
      tmp24 = 8;
    }
    if ((tmp23 === 85)) {
      tmp24 = 16;
    }
    if ((tmp24 === 0)) {
      if ((!((((((tmp23 === 97) || (tmp23 === 74)) || (tmp23 === 110)) || (tmp23 === 114)) || ((tmp23 === 94) && (tmp22 === tmp6))) || (tmp20 && (((((tmp23 === 68) || (tmp23 === 80)) || (tmp23 === 83)) || (tmp23 === 84)) || (tmp23 === 87)))))) {
        break;
      }
      tmp20 = (tmp23 === 97);
      tmp21 = (tmp23 === 94);
      tmp19 = false;
      tmp22 = ((tmp22 + 1) >>> 0);
      continue;
    }
    tmp20 = false;
    tmp21 = false;
    if (((tmp23 === 120) && ((tmp1 > ((tmp22 + 1) >>> 0)) && (tir_at(pat, ((tmp22 + 1) >>> 0)) === 120)))) {
      tmp19 = false;
    }
    if (tmp18) {
      tmp17 = ((tmp17 | tmp24) >>> 0);
    } else {
      tmp16 = ((tmp16 | tmp24) >>> 0);
    }
    tmp22 = ((tmp22 + 1) >>> 0);
  }
  if ((tmp22 >= tmp1)) {
    w.v.err = 114;
    w.v.erroff = tmp1;
    return;
  }
  if (((tir_at(pat, tmp22) !== 41) && (tir_at(pat, tmp22) !== 58))) {
    w.v.err = 111;
    w.v.erroff = ((tmp22 + 1) >>> 0);
    return;
  }
  if ((!tmp19)) {
    w.v.err = 1001;
    w.v.erroff = ((tmp22 + 1) >>> 0);
    return;
  }
  let tmp25 = ((((w.v.opts | tmp16) >>> 0) & ((~tmp17) >>> 0)) >>> 0);
  if ((tir_at(pat, tmp22) === 58)) {
    push_frame(w, 0, tmp25, tmp3, 0);
    at.v = ((tmp22 + 1) >>> 0);
    return;
  }
  w.v.opts = tmp25;
  let tmp26 = ((w.v.frames.n - 1) >>> 0);
  const tir_t3 = tmp26;
  tir_bound(w.v.frames.n, tir_t3);
  w.v.frames.a[tir_t3].qual = 0;
  at.v = ((tmp22 + 1) >>> 0);
}

export function open_region(w, kind, parent) {
  let tmp1 = w.v.regions.n;
  if ((tmp1 >= 8208)) {
    w.v.err = 1002;
    return 0;
  }
  tir_push(w.v.regions, 8208, tir_mk_obj, tir_new_Region(kind, parent, w.v.code.n, w.v.code.n));
  return tmp1;
}

export function parse(pat, popts, nltype, w) {
  let tmp1 = pat.n;
  let tmp2 = 0;
  const tir_t1 = alloc_node(w, NdNil, 0, 0, 0);
  tmp2 = tir_t1;
  let tmp3 = 0;
  const tir_t2 = alloc_node(w, NdGroup, 0, 0, 0);
  tmp3 = tir_t2;
  let tmp4 = 0;
  const tir_t3 = alloc_node(w, NdConcat, 0, 0, 0);
  tmp4 = tir_t3;
  add_child(w, tmp3, tmp4);
  w.v.root = tmp3;
  w.v.opts = popts;
  w.v.nltype = nltype;
  let tmp5 = popts;
  tir_push(w.v.frames, 251, tir_mk_obj, tir_new_Frame(tmp3, 0, tmp4, 0, tmp5, 0, 0));
  let tmp6 = 0;
  let tmp7 = false;
  let tmp8 = false;
  let tmp9 = new Esc();
  let tmp10 = new Quant();
  while (((tmp6 < tmp1) && (w.v.err === 0))) {
    let tmp11 = tir_at(pat, tmp6);
    if (tmp7) {
      if (((tmp11 === 92) && ((tmp1 > ((tmp6 + 1) >>> 0)) && (tir_at(pat, ((tmp6 + 1) >>> 0)) === 69)))) {
        tmp7 = false;
        tmp6 = ((tmp6 + 2) >>> 0);
        continue;
      }
      let tmp12 = ((tmp11) >>> 0);
      add_char(w, tmp12);
      tmp6 = ((tmp6 + 1) >>> 0);
      continue;
    }
    if ((((w.v.opts & 8) >>> 0) !== 0)) {
      const tir_t4 = ct(tmp11, 2);
      tmp8 = tir_t4;
      if ((tmp8 || (tmp11 === 35))) {
        const tir_t5 = tir_cell(tmp6);
        skip_gaps(pat, tir_t5, w);
        tmp6 = tir_t5.v;
        continue;
      }
    }
    if ((tmp11 === 40)) {
      const tir_t6 = tir_cell(tmp6);
      open_group(pat, tir_t6, w);
      tmp6 = tir_t6.v;
      continue;
    }
    if ((tmp11 === 41)) {
      if ((w.v.frames.n <= 1)) {
        w.v.err = 122;
        w.v.erroff = ((tmp6 + 1) >>> 0);
        continue;
      }
      close_group(w);
      tmp6 = ((tmp6 + 1) >>> 0);
      continue;
    }
    if ((tmp11 === 124)) {
      new_branch(w);
      tmp6 = ((tmp6 + 1) >>> 0);
      continue;
    }
    if ((tmp11 === 91)) {
      if (((tmp1 > ((tmp6 + 1) >>> 0)) && (((tir_at(pat, ((tmp6 + 1) >>> 0)) === 58) || (tir_at(pat, ((tmp6 + 1) >>> 0)) === 46)) || (tir_at(pat, ((tmp6 + 1) >>> 0)) === 61)))) {
        let tmp13 = 4294967295;
        const tir_t7 = posix_end(pat, ((tmp6 + 1) >>> 0));
        tmp13 = tir_t7;
        if ((tmp13 !== 4294967295)) {
          let tmp14 = 112;
          if ((tir_at(pat, ((tmp6 + 1) >>> 0)) !== 58)) {
            tmp14 = 113;
          }
          w.v.err = tmp14;
          w.v.erroff = ((tmp13 + 2) >>> 0);
          continue;
        }
      }
      let tmp15 = 0;
      const tir_t8 = tir_cell(tmp6);
      const tir_t9 = parse_class(pat, tir_t8, w);
      tmp6 = tir_t8.v;
      tmp15 = tir_t9;
      if ((w.v.err !== 0)) {
        continue;
      }
      attach_atom(w, NdClass, tmp15, 0);
      continue;
    }
    if ((tmp11 === 46)) {
      let tmp16 = NdAnyNoNL;
      if ((((w.v.opts & 4) >>> 0) !== 0)) {
        tmp16 = NdAny;
      }
      attach_atom(w, tmp16, 0, 0);
      tmp6 = ((tmp6 + 1) >>> 0);
      continue;
    }
    if ((tmp11 === 94)) {
      let tmp17 = NdCirc;
      if ((((w.v.opts & 2) >>> 0) !== 0)) {
        tmp17 = NdCircM;
      }
      attach_atom(w, tmp17, 0, 0);
      tmp6 = ((tmp6 + 1) >>> 0);
      continue;
    }
    if ((tmp11 === 36)) {
      let tmp18 = NdDoll;
      if ((((w.v.opts & 2) >>> 0) !== 0)) {
        tmp18 = NdDollM;
      } else {
        if ((((w.v.opts & 128) >>> 0) !== 0)) {
          tmp18 = NdDollE;
        }
      }
      attach_atom(w, tmp18, 0, 0);
      tmp6 = ((tmp6 + 1) >>> 0);
      continue;
    }
    if (((((tmp11 === 42) || (tmp11 === 43)) || (tmp11 === 63)) || (tmp11 === 123))) {
      const tir_t10 = tir_cell(tmp6);
      quantifier(pat, tir_t10, w);
      tmp6 = tir_t10.v;
      continue;
    }
    if ((tmp11 === 92)) {
      if ((tmp1 > ((tmp6 + 1) >>> 0))) {
        let tmp19 = tir_at(pat, ((tmp6 + 1) >>> 0));
        if ((tmp19 === 81)) {
          tmp7 = true;
          tmp6 = ((tmp6 + 2) >>> 0);
          continue;
        }
        if ((tmp19 === 69)) {
          tmp6 = ((tmp6 + 2) >>> 0);
          continue;
        }
      }
      const tir_t11 = tir_cell(tmp6);
      const tir_t12 = read_escape(pat, tir_t11, w, false);
      tmp6 = tir_t11.v;
      tmp9 = tir_t12;
      if ((w.v.err !== 0)) {
        continue;
      }
      attach_escape(w, tmp9.tir_clone());
      continue;
    }
    let tmp20 = ((tmp11) >>> 0);
    add_char(w, tmp20);
    tmp6 = ((tmp6 + 1) >>> 0);
  }
  if ((w.v.err !== 0)) {
    return;
  }
  if ((w.v.frames.n > 1)) {
    w.v.err = 114;
    w.v.erroff = tmp1;
    return;
  }
  let tmp21 = 0;
  let tmp22 = w.v.refs.n;
  let tmp23 = false;
  while ((tmp21 < tmp22)) {
    let tmp24 = tir_at(w.v.refs, tmp21).tir_clone();
    let tmp25 = (tmp24.num > w.v.ncap);
    if ((tmp24.num === 4294967295)) {
      const tir_t13 = name_taken(pat, tmp24.off, tmp24.nlen, w);
      tmp23 = tir_t13;
      tmp25 = (!tmp23);
    }
    if (tmp25) {
      w.v.err = 115;
      w.v.erroff = tmp24.off;
      return;
    }
    tmp21 = ((tmp21 + 1) >>> 0);
  }
  if ((tmp22 > 0)) {
    w.v.err = 1000;
    w.v.erroff = tir_at(w.v.refs, 0).off;
    return;
  }
  check_possess(w);
}

export function parse_class(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = ((at.v + 1) >>> 0);
  let tmp3 = false;
  let tmp4 = false;
  const tir_t1 = tir_cell(tmp2);
  const tir_t2 = tir_cell(tmp4);
  class_skip(pat, tir_t1, tir_t2);
  tmp2 = tir_t1.v;
  tmp4 = tir_t2.v;
  if ((((tmp2 < tmp1) && (tir_at(pat, tmp2) === 94)) && (!tmp4))) {
    tmp3 = true;
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  let tmp5 = 0;
  const tir_t3 = new_class(w);
  tmp5 = tir_t3;
  if ((w.v.err !== 0)) {
    return 0;
  }
  w.v.clselems = 0;
  w.v.clsrange = 0;
  w.v.clscrlf = 0;
  let tmp6 = ((Math.imul(tmp5, 32)) >>> 0);
  let tmp7 = (((w.v.opts & 1) >>> 0) !== 0);
  let tmp8 = true;
  let tmp9 = false;
  let tmp10 = 4294967295;
  let tmp11 = new Esc();
  while (((tmp2 < tmp1) && (w.v.err === 0))) {
    let tmp12 = tir_at(pat, tmp2);
    if (tmp4) {
      if (((tmp12 === 92) && ((tmp1 > ((tmp2 + 1) >>> 0)) && (tir_at(pat, ((tmp2 + 1) >>> 0)) === 69)))) {
        tmp4 = false;
        tmp2 = ((tmp2 + 2) >>> 0);
        continue;
      }
      tmp8 = false;
      tmp10 = ((tmp12) >>> 0);
      tmp2 = ((tmp2 + 1) >>> 0);
      note_element(w, tmp10, tmp10, false);
      set_range(w, tmp6, tmp10, tmp10, tmp7);
      continue;
    }
    if (((tmp12 === 93) && (!tmp8))) {
      tmp2 = ((tmp2 + 1) >>> 0);
      tmp9 = true;
      break;
    }
    if (((tmp12 === 91) && (tmp1 > ((tmp2 + 1) >>> 0)))) {
      let tmp13 = tir_at(pat, ((tmp2 + 1) >>> 0));
      if ((((tmp13 === 58) || (tmp13 === 46)) || (tmp13 === 61))) {
        let tmp14 = 4294967295;
        const tir_t4 = posix_end(pat, ((tmp2 + 1) >>> 0));
        tmp14 = tir_t4;
        if ((tmp14 !== 4294967295)) {
          if ((tmp13 !== 58)) {
            w.v.err = 113;
            w.v.erroff = ((tmp14 + 2) >>> 0);
            continue;
          }
          tmp8 = false;
          w.v.clsrange = 1;
          posix_item(w, pat, tmp2, tmp14, tmp6, tmp7);
          tmp2 = ((tmp14 + 2) >>> 0);
          class_after_set(w, tmp2, pat);
          continue;
        }
      }
    }
    if ((tmp12 === 92)) {
      if ((tmp1 > ((tmp2 + 1) >>> 0))) {
        let tmp15 = tir_at(pat, ((tmp2 + 1) >>> 0));
        if ((tmp15 === 81)) {
          tmp4 = true;
          tmp2 = ((tmp2 + 2) >>> 0);
          continue;
        }
        if ((tmp15 === 69)) {
          tmp2 = ((tmp2 + 2) >>> 0);
          continue;
        }
      }
      tmp8 = false;
      const tir_t5 = tir_cell(tmp2);
      const tir_t6 = read_escape(pat, tir_t5, w, true);
      tmp2 = tir_t5.v;
      tmp11 = tir_t6;
      if ((w.v.err !== 0)) {
        continue;
      }
      if ((tmp11.kind === EkChar)) {
        tmp10 = tmp11.val;
        const tir_t7 = tir_cell(tmp2);
        const tir_t8 = tir_cell(tmp4);
        class_element(w, tir_t7, tir_t8, pat, tmp6, tmp10, tmp7);
        tmp2 = tir_t7.v;
        tmp4 = tir_t8.v;
        continue;
      }
      let tmp16 = tmp11.val;
      let tmp17 = (tmp11.kind === EkNegSet);
      w.v.clsrange = 1;
      set_union(w, tmp6, tmp16, tmp17);
      class_after_set(w, tmp2, pat);
      continue;
    }
    tmp8 = false;
    tmp10 = ((tmp12) >>> 0);
    tmp2 = ((tmp2 + 1) >>> 0);
    const tir_t9 = tir_cell(tmp2);
    const tir_t10 = tir_cell(tmp4);
    class_element(w, tir_t9, tir_t10, pat, tmp6, tmp10, tmp7);
    tmp2 = tir_t9.v;
    tmp4 = tir_t10.v;
  }
  if ((w.v.err !== 0)) {
    return 0;
  }
  if ((!tmp9)) {
    w.v.err = 106;
    w.v.erroff = tmp1;
    return 0;
  }
  if ((w.v.clscrlf !== 0)) {
    let tmp18 = (tmp3 && ((w.v.clselems === 1) && (w.v.clsrange === 0)));
    if ((!tmp18)) {
      w.v.hascrlf = 1;
    }
  }
  if (tmp3) {
    let tmp19 = 0;
    while ((tmp19 < 32)) {
      let tmp20 = ((tmp6 + tmp19) >>> 0);
      const tir_t11 = tmp20;
      tir_bound(w.v.classes.n, tir_t11);
      w.v.classes.a[tir_t11] = ((~tir_at(w.v.classes, tmp20)) & 255);
      tmp19 = ((tmp19 + 1) >>> 0);
    }
  }
  at.v = tmp2;
  return tmp5;
}

export function pike_add(list, stk, seen, pool, rc, free, code, reps, subj, pos, novec, nltype, notbol, noteol, pc0, h0, mem, peak, cost, memlimit, costlimit) {
  let tmp1 = subj.n;
  let tmp2 = false;
  const tir_t1 = pike_defer(stk, pc0, h0, mem, peak, cost, memlimit, costlimit);
  tmp2 = tir_t1;
  if ((!tmp2)) {
    return false;
  }
  let tmp3 = tir_cmul((code.n), 2);
  while ((stk.v.n > 0)) {
    let tmp4 = new Th();
    tmp4 = tir_pop(stk.v);
    let tmp5 = tmp4.pc;
    let tmp6 = tmp4.h;
    let tmp7 = (tmp5 >>> 3);
    let tmp8 = tir_at(BITS, ((tmp5 & 7) >>> 0));
    if ((((tir_at(seen.v, tmp7) & tmp8) & 255) !== 0)) {
      const tir_t2 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t2;
      if ((!tmp2)) {
        return false;
      }
      continue;
    }
    const tir_t3 = tmp7;
    tir_bound(seen.v.n, tir_t3);
    seen.v.a[tir_t3] = ((tir_at(seen.v, tmp7) | tmp8) & 255);
    tmp3 = tir_csub(tmp3, 2);
    if ((1 > tir_csub(costlimit, cost.v))) {
      return false;
    }
    cost.v = tir_cadd(cost.v, 1);
    let tmp9 = tir_at(code, tmp5).tir_clone();
    const tir_t4 = tmp9.op;
    if (tir_t4 === OpChar) {
      const tir_t5 = pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t5;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpCharCI) {
      const tir_t6 = pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t6;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpClass) {
      const tir_t7 = pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t7;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpAny) {
      const tir_t8 = pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t8;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpAnyNoNL) {
      const tir_t9 = pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t9;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpAccept) {
      const tir_t10 = pike_park(list, tmp5, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t10;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpBsr) {
      const tir_t11 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t11;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpSplit) {
      const tir_t12 = tmp6;
      tir_bound(rc.v.n, tir_t12);
      rc.v.a[tir_t12] = ((tir_at(rc.v, tmp6) + 1) >>> 0);
      const tir_t13 = pike_defer(stk, tmp9.alt, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t13;
      if ((!tmp2)) {
        return false;
      }
      const tir_t14 = pike_defer(stk, tmp9.arg, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t14;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpJump) {
      const tir_t15 = pike_defer(stk, tmp9.arg, tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t15;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpSave) {
      const tir_t16 = tir_cell(tmp6);
      const tir_t17 = pike_write(pool, rc, free, novec, tir_t16, tmp9.arg, pos, mem, peak, cost, memlimit, costlimit);
      tmp6 = tir_t16.v;
      tmp2 = tir_t17;
      if ((!tmp2)) {
        return false;
      }
      const tir_t18 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t18;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpCirc) {
      if (((pos === 0) && (!notbol))) {
        const tir_t19 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t19;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t20 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t20;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpCircM) {
      let tmp10 = (!notbol);
      if ((pos !== 0)) {
        let tmp11 = 0;
        const tir_t21 = newline_before(subj, pos, nltype);
        tmp11 = tir_t21;
        tmp10 = ((pos !== tmp1) && (tmp11 !== 0));
      }
      if (tmp10) {
        const tir_t22 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t22;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t23 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t23;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpDoll) {
      let tmp12 = false;
      const tir_t24 = at_line_end(subj, pos, nltype);
      tmp12 = tir_t24;
      if (((!noteol) && tmp12)) {
        const tir_t25 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t25;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t26 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t26;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpDollE) {
      if (((!noteol) && (pos === tmp1))) {
        const tir_t27 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t27;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t28 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t28;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpDollM) {
      let tmp13 = (!noteol);
      if ((pos < tmp1)) {
        let tmp14 = 0;
        const tir_t29 = newline_at(subj, pos, nltype);
        tmp14 = tir_t29;
        tmp13 = (tmp14 !== 0);
      }
      if (tmp13) {
        const tir_t30 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t30;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t31 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t31;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpSod) {
      if ((pos === 0)) {
        const tir_t32 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t32;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t33 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t33;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpEod) {
      if ((pos === tmp1)) {
        const tir_t34 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t34;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t35 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t35;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpEodn) {
      let tmp15 = false;
      const tir_t36 = at_line_end(subj, pos, nltype);
      tmp15 = tir_t36;
      if (tmp15) {
        const tir_t37 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t37;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t38 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t38;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpWordB) {
      const tir_t39 = word_edge(subj, pos);
      tmp2 = tir_t39;
      if (tmp2) {
        const tir_t40 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t40;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t41 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t41;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpNotWordB) {
      const tir_t42 = word_edge(subj, pos);
      tmp2 = tir_t42;
      if ((!tmp2)) {
        const tir_t43 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t43;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t44 = pike_drop(rc, free, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t44;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpRepZero) {
      const tir_t45 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t45;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpRepEnter) {
      const tir_t46 = pike_defer(stk, ((tmp5 + 1) >>> 0), tmp6, mem, peak, cost, memlimit, costlimit);
      tmp2 = tir_t46;
      if ((!tmp2)) {
        return false;
      }
    } else if (tir_t4 === OpRepLoop) {
      let tmp16 = tir_at(reps, tmp9.arg).tir_clone();
      if (tmp16.greedy) {
        const tir_t47 = tmp6;
        tir_bound(rc.v.n, tir_t47);
        rc.v.a[tir_t47] = ((tir_at(rc.v, tmp6) + 1) >>> 0);
        const tir_t48 = pike_defer(stk, tmp16.after, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t48;
        if ((!tmp2)) {
          return false;
        }
        const tir_t49 = pike_defer(stk, tmp16.body, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t49;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t50 = tmp6;
        tir_bound(rc.v.n, tir_t50);
        rc.v.a[tir_t50] = ((tir_at(rc.v, tmp6) + 1) >>> 0);
        const tir_t51 = pike_defer(stk, tmp16.body, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t51;
        if ((!tmp2)) {
          return false;
        }
        const tir_t52 = pike_defer(stk, tmp16.after, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t52;
        if ((!tmp2)) {
          return false;
        }
      }
    } else if (tir_t4 === OpRepNext) {
      let tmp17 = tir_at(reps, tmp9.arg).tir_clone();
      if (tmp17.greedy) {
        const tir_t53 = tmp6;
        tir_bound(rc.v.n, tir_t53);
        rc.v.a[tir_t53] = ((tir_at(rc.v, tmp6) + 1) >>> 0);
        const tir_t54 = pike_defer(stk, tmp17.after, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t54;
        if ((!tmp2)) {
          return false;
        }
        const tir_t55 = pike_defer(stk, tmp17.body, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t55;
        if ((!tmp2)) {
          return false;
        }
      } else {
        const tir_t56 = tmp6;
        tir_bound(rc.v.n, tir_t56);
        rc.v.a[tir_t56] = ((tir_at(rc.v, tmp6) + 1) >>> 0);
        const tir_t57 = pike_defer(stk, tmp17.body, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t57;
        if ((!tmp2)) {
          return false;
        }
        const tir_t58 = pike_defer(stk, tmp17.after, tmp6, mem, peak, cost, memlimit, costlimit);
        tmp2 = tir_t58;
        if ((!tmp2)) {
          return false;
        }
      }
    }
  }
  return true;
}

export function pike_check(re, cert) {
  let tmp1 = false;
  const tir_t1 = pike_ok(re.tir_clone());
  tmp1 = tir_t1;
  if ((!tmp1)) {
    return CrIneligible;
  }
  if ((cert.config !== CfgPike)) {
    return CrConfig;
  }
  if ((cert.prices.n !== 0)) {
    return CrPrices;
  }
  let tmp2 = false;
  const tir_t2 = cert.complexity;
  if (tir_t2 === CcLinear) {
    tmp2 = true;
  } else if (tir_t2 === CcNotProvenLinear) {
    return CrNotLinear;
  }
  if ((!tmp2)) {
    return CrShape;
  }
  if ((!((((cert.cost.base === 1) && (cert.cost.c2 === 0)) && (cert.cost.c3 === 0)) && (cert.cost.c4 === 0)))) {
    return CrNotLinear;
  }
  let needed = new Cert();
  let tmp3 = false;
  const tir_t3 = tir_cell(needed);
  const tir_t4 = pike_price(re.tir_clone(), tir_t3);
  needed = tir_t3.v;
  tmp3 = tir_t4;
  if ((!tmp3)) {
    return CrOverflow;
  }
  let tmp4 = false;
  const tir_t5 = poly_ge(cert.cost.tir_clone(), needed.cost.tir_clone());
  tmp4 = tir_t5;
  if ((!tmp4)) {
    return CrTotalCost;
  }
  const tir_t6 = poly_eq(cert.stack.tir_clone(), needed.stack.tir_clone());
  tmp4 = tir_t6;
  if ((!tmp4)) {
    return CrTotalStack;
  }
  const tir_t7 = poly_eq(cert.trail.tir_clone(), needed.trail.tir_clone());
  tmp4 = tir_t7;
  if ((!tmp4)) {
    return CrTotalTrail;
  }
  const tir_t8 = poly_ge(cert.mem.tir_clone(), needed.mem.tir_clone());
  tmp4 = tir_t8;
  if ((!tmp4)) {
    return CrTotalMem;
  }
  return CrOk;
}

export function pike_defer(held, pcv, hv, mem, peak, cost, memlimit, costlimit) {
  let tmp1 = false;
  const tir_t1 = charge_grow(held.v.a.length, held.v.n, 8, 131396, mem, peak, cost, memlimit, costlimit);
  tmp1 = tir_t1;
  if ((!tmp1)) {
    return false;
  }
  tir_push(held.v, 131396, tir_mk_obj, tir_new_Th(pcv, hv));
  return true;
}

export function pike_drop(rc, free, h, mem, peak, cost, memlimit, costlimit) {
  if ((h === 4294967295)) {
    return true;
  }
  let tmp1 = ((tir_at(rc.v, h) - 1) >>> 0);
  const tir_t1 = h;
  tir_bound(rc.v.n, tir_t1);
  rc.v.a[tir_t1] = tmp1;
  if ((tmp1 === 0)) {
    let tmp2 = false;
    const tir_t2 = charge_grow(free.v.a.length, free.v.n, 4, 262796, mem, peak, cost, memlimit, costlimit);
    tmp2 = tir_t2;
    if ((!tmp2)) {
      return false;
    }
    tir_push(free.v, 262796, tir_mk_u32, h);
  }
  return true;
}

export function pike_hollow(re, which) {
  let tmp1 = tir_at(re.reps, which).tir_clone();
  let tmp2 = ((tmp1.after - 1) >>> 0);
  let tmp3 = re.code.n;
  let seen = new tir_Seq(tir_EMPTY_U8, 0);
  let tmp4 = (((tmp3 >>> 3) + 1) >>> 0);
  let tmp5 = 0;
  tir_reserve(seen, tmp4, 2147483647, tir_mk_u8);
  while ((tmp5 < tmp4)) {
    tir_push(seen, 2147483647, tir_mk_u8, 0);
    tmp5 = ((tmp5 + 1) >>> 0);
  }
  let pending = new tir_Seq(tir_EMPTY_U32, 0);
  tir_push(pending, 131396, tir_mk_u32, tmp1.body);
  let tmp6 = tir_cmul((tmp3), 2);
  while ((pending.n > 0)) {
    let tmp7 = 0;
    tmp7 = tir_pop(pending);
    if ((tmp7 >= tmp3)) {
      return true;
    }
    if ((tmp7 === tmp2)) {
      return true;
    }
    let tmp8 = (tmp7 >>> 3);
    let tmp9 = tir_at(BITS, ((tmp7 & 7) >>> 0));
    if ((((tir_at(seen, tmp8) & tmp9) & 255) !== 0)) {
      continue;
    }
    const tir_t1 = tmp8;
    tir_bound(seen.n, tir_t1);
    seen.a[tir_t1] = ((tir_at(seen, tmp8) | tmp9) & 255);
    tmp6 = tir_csub(tmp6, 2);
    let tmp10 = tir_at(re.code, tmp7).tir_clone();
    const tir_t2 = tmp10.op;
    if (tir_t2 === OpChar) {
      // nothing
    } else if (tir_t2 === OpCharCI) {
      // nothing
    } else if (tir_t2 === OpClass) {
      // nothing
    } else if (tir_t2 === OpAny) {
      // nothing
    } else if (tir_t2 === OpAnyNoNL) {
      // nothing
    } else if (tir_t2 === OpBsr) {
      // nothing
    } else if (tir_t2 === OpAccept) {
      // nothing
    } else if (tir_t2 === OpSplit) {
      tir_push(pending, 131396, tir_mk_u32, tmp10.arg);
      tir_push(pending, 131396, tir_mk_u32, tmp10.alt);
    } else if (tir_t2 === OpJump) {
      tir_push(pending, 131396, tir_mk_u32, tmp10.arg);
    } else if (tir_t2 === OpRepLoop) {
      let tmp11 = tir_at(re.reps, tmp10.arg).tir_clone();
      tir_push(pending, 131396, tir_mk_u32, tmp11.body);
      tir_push(pending, 131396, tir_mk_u32, tmp11.after);
    } else if (tir_t2 === OpRepNext) {
      let tmp12 = tir_at(re.reps, tmp10.arg).tir_clone();
      tir_push(pending, 131396, tir_mk_u32, tmp12.head);
      tir_push(pending, 131396, tir_mk_u32, tmp12.after);
    } else {
      tir_push(pending, 131396, tir_mk_u32, ((tmp7 + 1) >>> 0));
    }
  }
  return false;
}

export function pike_match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use) {
  let clist = new tir_Seq(tir_EMPTY_OBJ, 0);
  let nlist = new tir_Seq(tir_EMPTY_OBJ, 0);
  let stk = new tir_Seq(tir_EMPTY_OBJ, 0);
  let seen = new tir_Seq(tir_EMPTY_U8, 0);
  let pool = new tir_Seq(tir_EMPTY_U32, 0);
  let rc = new tir_Seq(tir_EMPTY_U32, 0);
  let free = new tir_Seq(tir_EMPTY_U32, 0);
  let tmp1 = 1;
  const tir_t1 = tir_cell(clist);
  const tir_t2 = tir_cell(nlist);
  const tir_t3 = tir_cell(stk);
  const tir_t4 = tir_cell(seen);
  const tir_t5 = tir_cell(pool);
  const tir_t6 = tir_cell(rc);
  const tir_t7 = tir_cell(free);
  const tir_t8 = pike_run(re.tir_clone(), subj, start, mopts, costlimit, stacklimit, memlimit, tir_t1, tir_t2, tir_t3, tir_t4, tir_t5, tir_t6, tir_t7, ov, use);
  clist = tir_t1.v;
  nlist = tir_t2.v;
  stk = tir_t3.v;
  seen = tir_t4.v;
  pool = tir_t5.v;
  rc = tir_t6.v;
  free = tir_t7.v;
  tmp1 = tir_t8;
  return tmp1;
}

export function pike_ok(re) {
  let tmp1 = 0;
  while ((tmp1 < re.reps.n)) {
    let tmp2 = tir_at(re.reps, tmp1).tir_clone();
    if (((tmp2.lo !== 0) || (tmp2.hi !== 4294967295))) {
      return false;
    }
    let tmp3 = true;
    const tir_t1 = pike_hollow(re.tir_clone(), tmp1);
    tmp3 = tir_t1;
    if (tmp3) {
      return false;
    }
    tmp1 = ((tmp1 + 1) >>> 0);
  }
  let tmp4 = 0;
  while ((tmp4 < re.code.n)) {
    if ((tir_at(re.code, tmp4).op === OpBsr)) {
      return false;
    }
    tmp4 = ((tmp4 + 1) >>> 0);
  }
  return true;
}

export function pike_park(held, pcv, hv, mem, peak, cost, memlimit, costlimit) {
  let tmp1 = false;
  const tir_t1 = charge_grow(held.v.a.length, held.v.n, 8, 65700, mem, peak, cost, memlimit, costlimit);
  tmp1 = tir_t1;
  if ((!tmp1)) {
    return false;
  }
  tir_push(held.v, 65700, tir_mk_obj, tir_new_Th(pcv, hv));
  return true;
}

export function pike_price(re, cert) {
  let over = false;
  let tmp1 = (re.code.n);
  let tmp2 = tir_cmul((((re.ncap + 1) >>> 0)), 2);
  let tmp3 = tir_cmul(tmp2, 4);
  let tmp4 = 0;
  let tmp5 = 0;
  while ((tmp5 < re.code.n)) {
    if ((tir_at(re.code, tmp5).op === OpSave)) {
      tmp4 = tir_cadd(tmp4, 1);
    }
    tmp5 = ((tmp5 + 1) >>> 0);
  }
  let room = new Room();
  const tir_t1 = tir_cell(room);
  const tir_t2 = tir_cell(over);
  pike_room(re.tir_clone(), tir_t1, tir_t2);
  room = tir_t1.v;
  over = tir_t2.v;
  let tmp6 = room.reserved;
  let tmp7 = (room.words);
  let tmp8 = 0;
  const tir_t3 = tir_cell(over);
  const tir_t4 = sat_add(tmp3, tmp7, tir_t3);
  over = tir_t3.v;
  tmp8 = tir_t4;
  let tmp9 = 0;
  const tir_t5 = tir_cell(over);
  const tir_t6 = sat_mul(tmp1, 2, tir_t5);
  over = tir_t5.v;
  tmp9 = tir_t6;
  let tmp10 = 0;
  const tir_t7 = tir_cell(over);
  const tir_t8 = sat_add(tmp4, 2, tir_t7);
  over = tir_t7.v;
  tmp10 = tir_t8;
  let tmp11 = 0;
  const tir_t9 = tir_cell(over);
  const tir_t10 = sat_mul(tmp10, tmp3, tir_t9);
  over = tir_t9.v;
  tmp11 = tir_t10;
  let tmp12 = 0;
  const tir_t11 = tir_cell(over);
  const tir_t12 = sat_add(tmp9, tmp11, tir_t11);
  over = tir_t11.v;
  tmp12 = tir_t12;
  tmp9 = tmp12;
  let tmp13 = 0;
  const tir_t13 = tir_cell(over);
  const tir_t14 = sat_add(tmp9, tmp7, tir_t13);
  over = tir_t13.v;
  tmp13 = tir_t14;
  tmp9 = tmp13;
  let tmp14 = 0;
  const tir_t15 = tir_cell(over);
  const tir_t16 = sat_add(tmp8, tmp3, tir_t15);
  over = tir_t15.v;
  tmp14 = tir_t16;
  let tmp15 = 0;
  const tir_t17 = tir_cell(over);
  const tir_t18 = sat_mul(tmp6, 3, tir_t17);
  over = tir_t17.v;
  tmp15 = tir_t18;
  let tmp16 = 0;
  const tir_t19 = tir_cell(over);
  const tir_t20 = sat_add(tmp14, tmp15, tir_t19);
  over = tir_t19.v;
  tmp16 = tir_t20;
  let tmp17 = 0;
  const tir_t21 = tir_cell(over);
  const tir_t22 = sat_mul(tmp6, 2, tir_t21);
  over = tir_t21.v;
  tmp17 = tir_t22;
  let tmp18 = 0;
  const tir_t23 = tir_cell(over);
  const tir_t24 = sat_add(tmp14, tmp17, tir_t23);
  over = tir_t23.v;
  tmp18 = tir_t24;
  if (over) {
    return false;
  }
  cert.v.config = CfgPike;
  cert.v.complexity = CcLinear;
  cert.v.cost = tir_new_Poly(1, tmp16, tmp9, 0, 0, 0);
  cert.v.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
  cert.v.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
  cert.v.mem = tir_new_Poly(1, tmp18, 0, 0, 0, 0);
  let empty = new tir_Seq(tir_EMPTY_OBJ, 0);
  cert.v.prices = empty;
  empty = new tir_Seq(tir_EMPTY_OBJ, 0);
  return true;
}

export function pike_room(re, room, over) {
  let tmp1 = (re.code.n);
  let tmp2 = tir_cmul((((re.ncap + 1) >>> 0)), 2);
  room.v.words = (((re.code.n >>> 3) + 1) >>> 0);
  let tmp3 = 0;
  if ((tmp1 > 0)) {
    let tmp4 = 0;
    const tir_t1 = sat_mul(tmp1, 2, over);
    tmp4 = tir_t1;
    let tmp5 = 0;
    const tir_t2 = sat_add(tmp4, 4, over);
    tmp5 = tir_t2;
    tmp3 = tmp5;
  }
  room.v.lists = tmp3;
  let tmp6 = 0;
  const tir_t3 = sat_mul(tmp1, 2, over);
  tmp6 = tir_t3;
  let tmp7 = 0;
  if ((tmp6 > 0)) {
    let tmp8 = 0;
    const tir_t4 = sat_mul(tmp6, 2, over);
    tmp8 = tir_t4;
    let tmp9 = 0;
    const tir_t5 = sat_add(tmp8, 4, over);
    tmp9 = tir_t5;
    tmp7 = tmp9;
  }
  room.v.stk = tmp7;
  let tmp10 = 0;
  const tir_t6 = sat_mul(tmp1, 4, over);
  tmp10 = tir_t6;
  let tmp11 = 0;
  const tir_t7 = sat_add(tmp10, 2, over);
  tmp11 = tir_t7;
  let tmp12 = tmp11;
  let tmp13 = 0;
  if ((tmp12 > 0)) {
    let tmp14 = 0;
    const tir_t8 = sat_mul(tmp12, 2, over);
    tmp14 = tir_t8;
    let tmp15 = 0;
    const tir_t9 = sat_add(tmp14, 4, over);
    tmp15 = tir_t9;
    tmp13 = tmp15;
  }
  room.v.tables = tmp13;
  let tmp16 = 0;
  const tir_t10 = sat_mul(tmp12, tmp2, over);
  tmp16 = tir_t10;
  let tmp17 = 0;
  if ((tmp16 > 0)) {
    let tmp18 = 0;
    const tir_t11 = sat_mul(tmp16, 2, over);
    tmp18 = tir_t11;
    let tmp19 = 0;
    const tir_t12 = sat_add(tmp18, 4, over);
    tmp19 = tir_t12;
    tmp17 = tmp19;
  }
  room.v.pool = tmp17;
  let tmp20 = 0;
  const tir_t13 = sat_mul(room.v.lists, 16, over);
  tmp20 = tir_t13;
  let tmp21 = tmp20;
  let tmp22 = 0;
  const tir_t14 = sat_mul(room.v.stk, 8, over);
  tmp22 = tir_t14;
  let tmp23 = 0;
  const tir_t15 = sat_add(tmp21, tmp22, over);
  tmp23 = tir_t15;
  tmp21 = tmp23;
  let tmp24 = 0;
  const tir_t16 = sat_mul(room.v.tables, 8, over);
  tmp24 = tir_t16;
  let tmp25 = 0;
  const tir_t17 = sat_add(tmp21, tmp24, over);
  tmp25 = tir_t17;
  tmp21 = tmp25;
  let tmp26 = 0;
  const tir_t18 = sat_mul(room.v.pool, 4, over);
  tmp26 = tir_t18;
  let tmp27 = 0;
  const tir_t19 = sat_add(tmp21, tmp26, over);
  tmp27 = tir_t19;
  tmp21 = tmp27;
  room.v.reserved = tmp21;
}

export function pike_run(re, subj, start, mopts, costlimit, stacklimit, memlimit, clist, nlist, stk, seen, pool, rc, free, ov, use) {
  let tmp1 = subj.n;
  let tmp2 = 0;
  let tmp3 = 0;
  let tmp4 = 0;
  use.v.cost = tmp2;
  use.v.stack = 0;
  use.v.mem = tmp4;
  if ((!re.pike)) {
    return 3;
  }
  if ((start > tmp1)) {
    return 3;
  }
  let code = re.code;
  let reps = re.reps;
  let classes = re.classes;
  let tmp5 = re.nltype;
  let tmp6 = re.ncap;
  let tmp7 = ((Math.imul(((tmp6 + 1) >>> 0), 2)) >>> 0);
  let tmp8 = ((((re.opts & 32) >>> 0) !== 0) || (((mopts & 16) >>> 0) !== 0));
  let tmp9 = (((mopts & 4) >>> 0) !== 0);
  let tmp10 = (((mopts & 8) >>> 0) !== 0);
  let tmp11 = (re.hascrlf === 0);
  let tmp12 = ((tmp5 === 2) || ((tmp5 === 3) || (tmp5 === 4)));
  let tmp13 = (((mopts & 1) >>> 0) !== 0);
  let tmp14 = (((mopts & 2) >>> 0) !== 0);
  tir_truncate(clist.v, 0);
  tir_truncate(nlist.v, 0);
  tir_truncate(stk.v, 0);
  tir_truncate(seen.v, 0);
  tir_truncate(pool.v, 0);
  tir_truncate(rc.v, 0);
  tir_truncate(free.v, 0);
  let tmp15 = (((code.n >>> 3) + 1) >>> 0);
  let tmp16 = tir_cadd(tir_cmul((tmp7), 4), (tmp15));
  if (((tmp16 > memlimit) || (tmp16 > costlimit))) {
    return 2;
  }
  tmp3 = tmp16;
  tmp4 = tmp16;
  tmp2 = tmp16;
  tir_reserve(ov.v, tmp7, 512, tir_mk_u32);
  tir_truncate(ov.v, 0);
  let tmp17 = 0;
  while ((tmp17 < tmp7)) {
    tir_push(ov.v, 512, tir_mk_u32, 4294967295);
    tmp17 = ((tmp17 + 1) >>> 0);
  }
  tir_reserve(seen.v, tmp15, 2147483647, tir_mk_u8);
  tmp17 = 0;
  while ((tmp17 < tmp15)) {
    tir_push(seen.v, 2147483647, tir_mk_u8, 0);
    tmp17 = ((tmp17 + 1) >>> 0);
  }
  let tmp18 = 4294967295;
  let tmp19 = true;
  let tmp20 = 1;
  let tmp21 = true;
  let tmp22 = start;
  let tmp23 = false;
  let tmp24 = tir_cmul((tmp7), 4);
  let tmp25 = (tmp15);
  let tmp26 = (re.crfirst !== 0);
  while (tmp21) {
    if ((tmp19 && ((!tmp8) || (tmp22 === start)))) {
      let tmp27 = false;
      if (((tmp22 > start) && (tmp12 && tmp11))) {
        if ((tmp26 && ((tir_at(subj, ((tmp22 - 1) >>> 0)) === 13) && ((tmp22 < tmp1) && (tir_at(subj, tmp22) === 10))))) {
          tmp27 = true;
        }
      }
      if ((!tmp27)) {
        let tmp28 = 4294967295;
        const tir_t1 = tir_cell(tmp3);
        const tir_t2 = tir_cell(tmp4);
        const tir_t3 = tir_cell(tmp2);
        const tir_t4 = pike_take(pool, rc, free, tmp7, tir_t1, tir_t2, tir_t3, memlimit, costlimit);
        tmp3 = tir_t1.v;
        tmp4 = tir_t2.v;
        tmp2 = tir_t3.v;
        tmp28 = tir_t4;
        if ((tmp28 === 4294967295)) {
          tmp20 = 2;
          tmp21 = false;
        } else {
          if ((tmp24 > tir_csub(costlimit, tmp2))) {
            tmp20 = 2;
            tmp21 = false;
          } else {
            tmp2 = tir_cadd(tmp2, tmp24);
            let tmp29 = ((Math.imul(tmp28, tmp7)) >>> 0);
            tmp17 = 0;
            while ((tmp17 < tmp7)) {
              const tir_t5 = ((tmp29 + tmp17) >>> 0);
              tir_bound(pool.v.n, tir_t5);
              pool.v.a[tir_t5] = 4294967295;
              tmp17 = ((tmp17 + 1) >>> 0);
            }
            const tir_t6 = tmp29;
            tir_bound(pool.v.n, tir_t6);
            pool.v.a[tir_t6] = tmp22;
            const tir_t7 = tir_cell(tmp3);
            const tir_t8 = tir_cell(tmp4);
            const tir_t9 = tir_cell(tmp2);
            const tir_t10 = pike_add(clist, stk, seen, pool, rc, free, code, reps, subj, tmp22, tmp7, tmp5, tmp13, tmp14, 0, tmp28, tir_t7, tir_t8, tir_t9, memlimit, costlimit);
            tmp3 = tir_t7.v;
            tmp4 = tir_t8.v;
            tmp2 = tir_t9.v;
            tmp23 = tir_t10;
            if ((!tmp23)) {
              tmp20 = 2;
              tmp21 = false;
            }
          }
        }
      }
    }
    if (tmp21) {
      if ((tmp25 > tir_csub(costlimit, tmp2))) {
        tmp20 = 2;
        tmp21 = false;
      } else {
        tmp2 = tir_cadd(tmp2, tmp25);
        tmp17 = 0;
        while ((tmp17 < tmp15)) {
          const tir_t11 = tmp17;
          tir_bound(seen.v.n, tir_t11);
          seen.v.a[tir_t11] = 0;
          tmp17 = ((tmp17 + 1) >>> 0);
        }
      }
    }
    let tmp30 = 0;
    while ((tmp21 && (tmp30 < clist.v.n))) {
      let tmp31 = tir_at(clist.v, tmp30).tir_clone();
      let tmp32 = tmp31.pc;
      let tmp33 = tmp31.h;
      if ((1 > tir_csub(costlimit, tmp2))) {
        tmp20 = 2;
        tmp21 = false;
        continue;
      }
      tmp2 = tir_cadd(tmp2, 1);
      let tmp34 = tir_at(code, tmp32).tir_clone();
      const tir_t12 = tmp34.op;
      if (tir_t12 === OpChar) {
        if (((tmp22 < tmp1) && (tir_at(subj, tmp22) === ((tmp34.arg) & 255)))) {
          const tir_t13 = tir_cell(tmp3);
          const tir_t14 = tir_cell(tmp4);
          const tir_t15 = tir_cell(tmp2);
          const tir_t16 = pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, ((tmp22 + 1) >>> 0), tmp7, tmp5, tmp13, tmp14, ((tmp32 + 1) >>> 0), tmp33, tir_t13, tir_t14, tir_t15, memlimit, costlimit);
          tmp3 = tir_t13.v;
          tmp4 = tir_t14.v;
          tmp2 = tir_t15.v;
          tmp23 = tir_t16;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        } else {
          const tir_t17 = tir_cell(tmp3);
          const tir_t18 = tir_cell(tmp4);
          const tir_t19 = tir_cell(tmp2);
          const tir_t20 = pike_drop(rc, free, tmp33, tir_t17, tir_t18, tir_t19, memlimit, costlimit);
          tmp3 = tir_t17.v;
          tmp4 = tir_t18.v;
          tmp2 = tir_t19.v;
          tmp23 = tir_t20;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        }
      } else if (tir_t12 === OpCharCI) {
        if (((tmp22 < tmp1) && (tir_at(LOWER, ((tir_at(subj, tmp22)) >>> 0)) === ((tmp34.arg) & 255)))) {
          const tir_t21 = tir_cell(tmp3);
          const tir_t22 = tir_cell(tmp4);
          const tir_t23 = tir_cell(tmp2);
          const tir_t24 = pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, ((tmp22 + 1) >>> 0), tmp7, tmp5, tmp13, tmp14, ((tmp32 + 1) >>> 0), tmp33, tir_t21, tir_t22, tir_t23, memlimit, costlimit);
          tmp3 = tir_t21.v;
          tmp4 = tir_t22.v;
          tmp2 = tir_t23.v;
          tmp23 = tir_t24;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        } else {
          const tir_t25 = tir_cell(tmp3);
          const tir_t26 = tir_cell(tmp4);
          const tir_t27 = tir_cell(tmp2);
          const tir_t28 = pike_drop(rc, free, tmp33, tir_t25, tir_t26, tir_t27, memlimit, costlimit);
          tmp3 = tir_t25.v;
          tmp4 = tir_t26.v;
          tmp2 = tir_t27.v;
          tmp23 = tir_t28;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        }
      } else if (tir_t12 === OpClass) {
        let tmp35 = false;
        if ((tmp22 < tmp1)) {
          const tir_t29 = class_has(classes, tmp34.arg, tir_at(subj, tmp22));
          tmp35 = tir_t29;
        }
        if (((tmp22 < tmp1) && tmp35)) {
          const tir_t30 = tir_cell(tmp3);
          const tir_t31 = tir_cell(tmp4);
          const tir_t32 = tir_cell(tmp2);
          const tir_t33 = pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, ((tmp22 + 1) >>> 0), tmp7, tmp5, tmp13, tmp14, ((tmp32 + 1) >>> 0), tmp33, tir_t30, tir_t31, tir_t32, memlimit, costlimit);
          tmp3 = tir_t30.v;
          tmp4 = tir_t31.v;
          tmp2 = tir_t32.v;
          tmp23 = tir_t33;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        } else {
          const tir_t34 = tir_cell(tmp3);
          const tir_t35 = tir_cell(tmp4);
          const tir_t36 = tir_cell(tmp2);
          const tir_t37 = pike_drop(rc, free, tmp33, tir_t34, tir_t35, tir_t36, memlimit, costlimit);
          tmp3 = tir_t34.v;
          tmp4 = tir_t35.v;
          tmp2 = tir_t36.v;
          tmp23 = tir_t37;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        }
      } else if (tir_t12 === OpAny) {
        if (((tmp22 < tmp1) && true)) {
          const tir_t38 = tir_cell(tmp3);
          const tir_t39 = tir_cell(tmp4);
          const tir_t40 = tir_cell(tmp2);
          const tir_t41 = pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, ((tmp22 + 1) >>> 0), tmp7, tmp5, tmp13, tmp14, ((tmp32 + 1) >>> 0), tmp33, tir_t38, tir_t39, tir_t40, memlimit, costlimit);
          tmp3 = tir_t38.v;
          tmp4 = tir_t39.v;
          tmp2 = tir_t40.v;
          tmp23 = tir_t41;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        } else {
          const tir_t42 = tir_cell(tmp3);
          const tir_t43 = tir_cell(tmp4);
          const tir_t44 = tir_cell(tmp2);
          const tir_t45 = pike_drop(rc, free, tmp33, tir_t42, tir_t43, tir_t44, memlimit, costlimit);
          tmp3 = tir_t42.v;
          tmp4 = tir_t43.v;
          tmp2 = tir_t44.v;
          tmp23 = tir_t45;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        }
      } else if (tir_t12 === OpAnyNoNL) {
        let tmp36 = 0;
        if ((tmp22 < tmp1)) {
          const tir_t46 = newline_at(subj, tmp22, tmp5);
          tmp36 = tir_t46;
        }
        if (((tmp22 < tmp1) && (tmp36 === 0))) {
          const tir_t47 = tir_cell(tmp3);
          const tir_t48 = tir_cell(tmp4);
          const tir_t49 = tir_cell(tmp2);
          const tir_t50 = pike_add(nlist, stk, seen, pool, rc, free, code, reps, subj, ((tmp22 + 1) >>> 0), tmp7, tmp5, tmp13, tmp14, ((tmp32 + 1) >>> 0), tmp33, tir_t47, tir_t48, tir_t49, memlimit, costlimit);
          tmp3 = tir_t47.v;
          tmp4 = tir_t48.v;
          tmp2 = tir_t49.v;
          tmp23 = tir_t50;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        } else {
          const tir_t51 = tir_cell(tmp3);
          const tir_t52 = tir_cell(tmp4);
          const tir_t53 = tir_cell(tmp2);
          const tir_t54 = pike_drop(rc, free, tmp33, tir_t51, tir_t52, tir_t53, memlimit, costlimit);
          tmp3 = tir_t51.v;
          tmp4 = tir_t52.v;
          tmp2 = tir_t53.v;
          tmp23 = tir_t54;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        }
      } else if (tir_t12 === OpAccept) {
        let tmp37 = tir_at(pool.v, ((Math.imul(tmp33, tmp7)) >>> 0));
        let tmp38 = (tmp37 === tmp22);
        let tmp39 = (tmp38 && (tmp9 || (tmp10 && (tmp37 === start))));
        if (tmp39) {
          const tir_t55 = tir_cell(tmp3);
          const tir_t56 = tir_cell(tmp4);
          const tir_t57 = tir_cell(tmp2);
          const tir_t58 = pike_drop(rc, free, tmp33, tir_t55, tir_t56, tir_t57, memlimit, costlimit);
          tmp3 = tir_t55.v;
          tmp4 = tir_t56.v;
          tmp2 = tir_t57.v;
          tmp23 = tir_t58;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          }
        } else {
          let tmp40 = tmp33;
          const tir_t59 = tir_cell(tmp40);
          const tir_t60 = tir_cell(tmp3);
          const tir_t61 = tir_cell(tmp4);
          const tir_t62 = tir_cell(tmp2);
          const tir_t63 = pike_write(pool, rc, free, tmp7, tir_t59, 1, tmp22, tir_t60, tir_t61, tir_t62, memlimit, costlimit);
          tmp40 = tir_t59.v;
          tmp3 = tir_t60.v;
          tmp4 = tir_t61.v;
          tmp2 = tir_t62.v;
          tmp23 = tir_t63;
          if ((!tmp23)) {
            tmp20 = 2;
            tmp21 = false;
          } else {
            const tir_t64 = tir_cell(tmp3);
            const tir_t65 = tir_cell(tmp4);
            const tir_t66 = tir_cell(tmp2);
            const tir_t67 = pike_drop(rc, free, tmp18, tir_t64, tir_t65, tir_t66, memlimit, costlimit);
            tmp3 = tir_t64.v;
            tmp4 = tir_t65.v;
            tmp2 = tir_t66.v;
            tmp23 = tir_t67;
            if ((!tmp23)) {
              tmp20 = 2;
              tmp21 = false;
            }
            if (tmp21) {
              tmp18 = tmp40;
              tmp19 = false;
              tmp20 = 0;
              let tmp41 = ((tmp30 + 1) >>> 0);
              while ((tmp21 && (tmp41 < clist.v.n))) {
                const tir_t68 = tir_cell(tmp3);
                const tir_t69 = tir_cell(tmp4);
                const tir_t70 = tir_cell(tmp2);
                const tir_t71 = pike_drop(rc, free, tir_at(clist.v, tmp41).h, tir_t68, tir_t69, tir_t70, memlimit, costlimit);
                tmp3 = tir_t68.v;
                tmp4 = tir_t69.v;
                tmp2 = tir_t70.v;
                tmp23 = tir_t71;
                if ((!tmp23)) {
                  tmp20 = 2;
                  tmp21 = false;
                }
                tmp41 = ((tmp41 + 1) >>> 0);
              }
              tmp30 = clist.v.n;
              continue;
            }
          }
        }
      } else {
        const tir_t72 = tir_cell(tmp3);
        const tir_t73 = tir_cell(tmp4);
        const tir_t74 = tir_cell(tmp2);
        const tir_t75 = pike_drop(rc, free, tmp33, tir_t72, tir_t73, tir_t74, memlimit, costlimit);
        tmp3 = tir_t72.v;
        tmp4 = tir_t73.v;
        tmp2 = tir_t74.v;
        tmp23 = tir_t75;
        if ((!tmp23)) {
          tmp20 = 2;
          tmp21 = false;
        }
      }
      tmp30 = ((tmp30 + 1) >>> 0);
    }
    if (tmp21) {
      tir_truncate(clist.v, 0);
      const tir_t76 = clist.v;
      clist.v = nlist.v;
      nlist.v = tir_t76;
      if ((tmp22 >= tmp1)) {
        tmp21 = false;
      } else {
        if (((clist.v.n === 0) && ((!tmp19) || tmp8))) {
          tmp21 = false;
        }
      }
    }
    tmp22 = ((tmp22 + 1) >>> 0);
  }
  if ((tmp20 === 0)) {
    if ((tmp24 > tir_csub(costlimit, tmp2))) {
      tmp20 = 2;
    } else {
      tmp2 = tir_cadd(tmp2, tmp24);
      tmp17 = 0;
      while ((tmp17 < tmp7)) {
        const tir_t77 = tmp17;
        tir_bound(ov.v.n, tir_t77);
        ov.v.a[tir_t77] = tir_at(pool.v, ((((Math.imul(tmp18, tmp7)) >>> 0) + tmp17) >>> 0));
        tmp17 = ((tmp17 + 1) >>> 0);
      }
    }
  }
  use.v.cost = tmp2;
  use.v.stack = 0;
  use.v.mem = tmp4;
  return tmp20;
}

export function pike_take(pool, rc, free, novec, mem, peak, cost, memlimit, costlimit) {
  if ((free.v.n > 0)) {
    let tmp1 = 0;
    tmp1 = tir_pop(free.v);
    const tir_t1 = tmp1;
    tir_bound(rc.v.n, tir_t1);
    rc.v.a[tir_t1] = 1;
    return tmp1;
  }
  let tmp2 = rc.v.n;
  if ((tmp2 >= 262796)) {
    return 4294967295;
  }
  let tmp3 = false;
  const tir_t2 = charge_grow(rc.v.a.length, rc.v.n, 4, 262796, mem, peak, cost, memlimit, costlimit);
  tmp3 = tir_t2;
  if ((!tmp3)) {
    return 4294967295;
  }
  tir_push(rc.v, 262796, tir_mk_u32, 1);
  let tmp4 = 0;
  while ((tmp4 < novec)) {
    const tir_t3 = charge_grow(pool.v.a.length, pool.v.n, 4, 134549508, mem, peak, cost, memlimit, costlimit);
    tmp3 = tir_t3;
    if ((!tmp3)) {
      return 4294967295;
    }
    tir_push(pool.v, 134549508, tir_mk_u32, 4294967295);
    tmp4 = ((tmp4 + 1) >>> 0);
  }
  return tmp2;
}

export function pike_write(pool, rc, free, novec, h, slot, value, mem, peak, cost, memlimit, costlimit) {
  if ((tir_at(rc.v, h.v) > 1)) {
    let tmp1 = tir_cmul((novec), 4);
    if ((tmp1 > tir_csub(costlimit, cost.v))) {
      return false;
    }
    cost.v = tir_cadd(cost.v, tmp1);
    let tmp2 = 4294967295;
    const tir_t1 = pike_take(pool, rc, free, novec, mem, peak, cost, memlimit, costlimit);
    tmp2 = tir_t1;
    if ((tmp2 === 4294967295)) {
      return false;
    }
    let tmp3 = ((Math.imul(tmp2, novec)) >>> 0);
    let tmp4 = ((Math.imul(h.v, novec)) >>> 0);
    let tmp5 = 0;
    while ((tmp5 < novec)) {
      const tir_t2 = ((tmp3 + tmp5) >>> 0);
      tir_bound(pool.v.n, tir_t2);
      pool.v.a[tir_t2] = tir_at(pool.v, ((tmp4 + tmp5) >>> 0));
      tmp5 = ((tmp5 + 1) >>> 0);
    }
    const tir_t3 = h.v;
    tir_bound(rc.v.n, tir_t3);
    rc.v.a[tir_t3] = ((tir_at(rc.v, h.v) - 1) >>> 0);
    h.v = tmp2;
  }
  const tir_t4 = ((((Math.imul(h.v, novec)) >>> 0) + slot) >>> 0);
  tir_bound(pool.v.n, tir_t4);
  pool.v.a[tir_t4] = value;
  return true;
}

export function plan_lowering(w, endanchored) {
  let tmp1 = w.v.nodes.n;
  let tmp2 = 0;
  while ((tmp2 < tmp1)) {
    tir_push(w.v.sizes, 8208, tir_mk_obj, tir_new_Size(0, 0, 0, 0, 0, 0, false, 0, false));
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  tir_push(w.v.order, 8208, tir_mk_u32, w.v.root);
  let tmp3 = 0;
  let tmp4 = 8208;
  while (((tmp3 < w.v.order.n) && (tmp4 > 0))) {
    tmp4 = tir_csub(tmp4, 1);
    let tmp5 = tir_at(w.v.nodes, tir_at(w.v.order, tmp3)).first;
    let tmp6 = 8208;
    while (((tmp5 !== 0) && (tmp6 > 0))) {
      tmp6 = tir_csub(tmp6, 1);
      if ((w.v.order.n >= 8208)) {
        w.v.err = 1003;
        return;
      }
      tir_push(w.v.order, 8208, tir_mk_u32, tmp5);
      tmp5 = tir_at(w.v.nodes, tmp5).nxt;
    }
    if ((tmp6 === 0)) {
      w.v.err = 1003;
      return;
    }
    tmp3 = ((tmp3 + 1) >>> 0);
  }
  if ((tmp4 === 0)) {
    w.v.err = 1003;
    return;
  }
  let tmp7 = w.v.order.n;
  while ((tmp7 > 0)) {
    tmp7 = ((tmp7 - 1) >>> 0);
    let tmp8 = tir_at(w.v.order, tmp7);
    size_node(w, tmp8);
  }
  let tmp9 = tir_at(w.v.sizes, w.v.root).tir_clone();
  let tmp10 = tir_cadd(tmp9.code, 1);
  if (endanchored) {
    tmp10 = tir_cadd(tmp10, 1);
  }
  let tmp11 = tir_cadd(tmp9.regions, 1);
  let tmp12 = tmp9.reps;
  let tmp13 = tir_cadd(tir_cmul((((w.v.ncap + 1) >>> 0)), 2), tir_cmul(tmp12, 2));
  w.v.fitcode = tmp10;
  w.v.fitregion = tmp11;
  w.v.fitrep = tmp12;
  w.v.fitvisit = tmp9.visits;
  w.v.fitjobs = tmp9.depth;
  w.v.fitpatch = tmp9.patches;
  let tmp14 = true;
  if ((tmp10 > 32848)) {
    tmp14 = false;
  }
  if ((tmp11 > 8208)) {
    tmp14 = false;
  }
  if ((tmp12 > 4096)) {
    tmp14 = false;
  }
  if ((tmp13 > 8704)) {
    tmp14 = false;
  }
  if ((tmp9.visits > 65664)) {
    tmp14 = false;
  }
  if ((tmp9.depth > 2048)) {
    tmp14 = false;
  }
  if ((tmp9.patches > 4096)) {
    tmp14 = false;
  }
  w.v.lowfits = tmp14;
  w.v.blockers = tmp9.blockers;
  w.v.lowdec = 0;
  w.v.lowering = false;
  if (tmp9.needs) {
    if ((tmp9.blockers !== 0)) {
      w.v.lowdec = 2;
    } else {
      if (tmp14) {
        w.v.lowdec = 1;
        w.v.lowering = true;
      } else {
        w.v.lowdec = 3;
      }
    }
  }
  w.v.predicted = (w.v.lowering || (!tmp9.needs));
}

export function poly_add(a, b, over) {
  let out = new Poly();
  out.base = a.base;
  if ((b.base > a.base)) {
    out.base = b.base;
  }
  let tmp1 = 0;
  const tir_t1 = sat_add(a.c0, b.c0, over);
  tmp1 = tir_t1;
  out.c0 = tmp1;
  let tmp2 = 0;
  const tir_t2 = sat_add(a.c1, b.c1, over);
  tmp2 = tir_t2;
  out.c1 = tmp2;
  let tmp3 = 0;
  const tir_t3 = sat_add(a.c2, b.c2, over);
  tmp3 = tir_t3;
  out.c2 = tmp3;
  let tmp4 = 0;
  const tir_t4 = sat_add(a.c3, b.c3, over);
  tmp4 = tir_t4;
  out.c3 = tmp4;
  let tmp5 = 0;
  const tir_t5 = sat_add(a.c4, b.c4, over);
  tmp5 = tir_t5;
  out.c4 = tmp5;
  let done = new Poly();
  const tir_t6 = poly_norm(out.tir_clone());
  done = tir_t6;
  return done.tir_clone();
}

export function poly_eq(a, b) {
  if ((a.base !== b.base)) {
    return false;
  }
  if ((a.c0 !== b.c0)) {
    return false;
  }
  if ((a.c1 !== b.c1)) {
    return false;
  }
  if ((a.c2 !== b.c2)) {
    return false;
  }
  if ((a.c3 !== b.c3)) {
    return false;
  }
  if ((a.c4 !== b.c4)) {
    return false;
  }
  return true;
}

export function poly_ge(a, b) {
  if ((a.base < b.base)) {
    return false;
  }
  if ((a.c0 < b.c0)) {
    return false;
  }
  if ((a.c1 < b.c1)) {
    return false;
  }
  if ((a.c2 < b.c2)) {
    return false;
  }
  if ((a.c3 < b.c3)) {
    return false;
  }
  if ((a.c4 < b.c4)) {
    return false;
  }
  return true;
}

export function poly_mul(a, b, over) {
  let out = tir_new_Poly(1, 0, 0, 0, 0, 0);
  let base = 0;
  const tir_t1 = sat_mul(a.base, b.base, over);
  base = tir_t1;
  out.base = base;
  if (((a.c0 !== 0) && (b.c0 !== 0))) {
    let tmp1 = 0;
    const tir_t2 = sat_mul(a.c0, b.c0, over);
    tmp1 = tir_t2;
    let tmp2 = 0;
    const tir_t3 = sat_add(out.c0, tmp1, over);
    tmp2 = tir_t3;
    out.c0 = tmp2;
  }
  if (((a.c0 !== 0) && (b.c1 !== 0))) {
    let tmp3 = 0;
    const tir_t4 = sat_mul(a.c0, b.c1, over);
    tmp3 = tir_t4;
    let tmp4 = 0;
    const tir_t5 = sat_add(out.c1, tmp3, over);
    tmp4 = tir_t5;
    out.c1 = tmp4;
  }
  if (((a.c0 !== 0) && (b.c2 !== 0))) {
    let tmp5 = 0;
    const tir_t6 = sat_mul(a.c0, b.c2, over);
    tmp5 = tir_t6;
    let tmp6 = 0;
    const tir_t7 = sat_add(out.c2, tmp5, over);
    tmp6 = tir_t7;
    out.c2 = tmp6;
  }
  if (((a.c0 !== 0) && (b.c3 !== 0))) {
    let tmp7 = 0;
    const tir_t8 = sat_mul(a.c0, b.c3, over);
    tmp7 = tir_t8;
    let tmp8 = 0;
    const tir_t9 = sat_add(out.c3, tmp7, over);
    tmp8 = tir_t9;
    out.c3 = tmp8;
  }
  if (((a.c0 !== 0) && (b.c4 !== 0))) {
    let tmp9 = 0;
    const tir_t10 = sat_mul(a.c0, b.c4, over);
    tmp9 = tir_t10;
    let tmp10 = 0;
    const tir_t11 = sat_add(out.c4, tmp9, over);
    tmp10 = tir_t11;
    out.c4 = tmp10;
  }
  if (((a.c1 !== 0) && (b.c0 !== 0))) {
    let tmp11 = 0;
    const tir_t12 = sat_mul(a.c1, b.c0, over);
    tmp11 = tir_t12;
    let tmp12 = 0;
    const tir_t13 = sat_add(out.c1, tmp11, over);
    tmp12 = tir_t13;
    out.c1 = tmp12;
  }
  if (((a.c1 !== 0) && (b.c1 !== 0))) {
    let tmp13 = 0;
    const tir_t14 = sat_mul(a.c1, b.c1, over);
    tmp13 = tir_t14;
    let tmp14 = 0;
    const tir_t15 = sat_add(out.c2, tmp13, over);
    tmp14 = tir_t15;
    out.c2 = tmp14;
  }
  if (((a.c1 !== 0) && (b.c2 !== 0))) {
    let tmp15 = 0;
    const tir_t16 = sat_mul(a.c1, b.c2, over);
    tmp15 = tir_t16;
    let tmp16 = 0;
    const tir_t17 = sat_add(out.c3, tmp15, over);
    tmp16 = tir_t17;
    out.c3 = tmp16;
  }
  if (((a.c1 !== 0) && (b.c3 !== 0))) {
    let tmp17 = 0;
    const tir_t18 = sat_mul(a.c1, b.c3, over);
    tmp17 = tir_t18;
    let tmp18 = 0;
    const tir_t19 = sat_add(out.c4, tmp17, over);
    tmp18 = tir_t19;
    out.c4 = tmp18;
  }
  if (((a.c1 !== 0) && (b.c4 !== 0))) {
    over.v = true;
  }
  if (((a.c2 !== 0) && (b.c0 !== 0))) {
    let tmp19 = 0;
    const tir_t20 = sat_mul(a.c2, b.c0, over);
    tmp19 = tir_t20;
    let tmp20 = 0;
    const tir_t21 = sat_add(out.c2, tmp19, over);
    tmp20 = tir_t21;
    out.c2 = tmp20;
  }
  if (((a.c2 !== 0) && (b.c1 !== 0))) {
    let tmp21 = 0;
    const tir_t22 = sat_mul(a.c2, b.c1, over);
    tmp21 = tir_t22;
    let tmp22 = 0;
    const tir_t23 = sat_add(out.c3, tmp21, over);
    tmp22 = tir_t23;
    out.c3 = tmp22;
  }
  if (((a.c2 !== 0) && (b.c2 !== 0))) {
    let tmp23 = 0;
    const tir_t24 = sat_mul(a.c2, b.c2, over);
    tmp23 = tir_t24;
    let tmp24 = 0;
    const tir_t25 = sat_add(out.c4, tmp23, over);
    tmp24 = tir_t25;
    out.c4 = tmp24;
  }
  if (((a.c2 !== 0) && (b.c3 !== 0))) {
    over.v = true;
  }
  if (((a.c2 !== 0) && (b.c4 !== 0))) {
    over.v = true;
  }
  if (((a.c3 !== 0) && (b.c0 !== 0))) {
    let tmp25 = 0;
    const tir_t26 = sat_mul(a.c3, b.c0, over);
    tmp25 = tir_t26;
    let tmp26 = 0;
    const tir_t27 = sat_add(out.c3, tmp25, over);
    tmp26 = tir_t27;
    out.c3 = tmp26;
  }
  if (((a.c3 !== 0) && (b.c1 !== 0))) {
    let tmp27 = 0;
    const tir_t28 = sat_mul(a.c3, b.c1, over);
    tmp27 = tir_t28;
    let tmp28 = 0;
    const tir_t29 = sat_add(out.c4, tmp27, over);
    tmp28 = tir_t29;
    out.c4 = tmp28;
  }
  if (((a.c3 !== 0) && (b.c2 !== 0))) {
    over.v = true;
  }
  if (((a.c3 !== 0) && (b.c3 !== 0))) {
    over.v = true;
  }
  if (((a.c3 !== 0) && (b.c4 !== 0))) {
    over.v = true;
  }
  if (((a.c4 !== 0) && (b.c0 !== 0))) {
    let tmp29 = 0;
    const tir_t30 = sat_mul(a.c4, b.c0, over);
    tmp29 = tir_t30;
    let tmp30 = 0;
    const tir_t31 = sat_add(out.c4, tmp29, over);
    tmp30 = tir_t31;
    out.c4 = tmp30;
  }
  if (((a.c4 !== 0) && (b.c1 !== 0))) {
    over.v = true;
  }
  if (((a.c4 !== 0) && (b.c2 !== 0))) {
    over.v = true;
  }
  if (((a.c4 !== 0) && (b.c3 !== 0))) {
    over.v = true;
  }
  if (((a.c4 !== 0) && (b.c4 !== 0))) {
    over.v = true;
  }
  let done = new Poly();
  const tir_t32 = poly_norm(out.tir_clone());
  done = tir_t32;
  return done.tir_clone();
}

export function poly_norm(p) {
  if ((((((p.c0 === 0) && (p.c1 === 0)) && (p.c2 === 0)) && (p.c3 === 0)) && (p.c4 === 0))) {
    return tir_new_Poly(1, 0, 0, 0, 0, 0);
  }
  return p.tir_clone();
}

export function poly_value(p, n) {
  if ((((((p.c0 === 0) && (p.c1 === 0)) && (p.c2 === 0)) && (p.c3 === 0)) && (p.c4 === 0))) {
    return tir_new_Bound(true, 0);
  }
  let rise = new Bound();
  const tir_t1 = bound_add(tir_new_Bound(true, n), tir_new_Bound(true, 1));
  rise = tir_t1;
  let power = tir_new_Bound(true, 1);
  let total = tir_new_Bound(true, p.c0);
  if (((((p.c1 !== 0) || (p.c2 !== 0)) || (p.c3 !== 0)) || (p.c4 !== 0))) {
    let tmp1 = new Bound();
    const tir_t2 = bound_mul(power.tir_clone(), rise.tir_clone());
    tmp1 = tir_t2;
    power = tmp1.tir_clone();
    if ((p.c1 !== 0)) {
      let tmp2 = new Bound();
      const tir_t3 = bound_mul(tir_new_Bound(true, p.c1), power.tir_clone());
      tmp2 = tir_t3;
      let tmp3 = new Bound();
      const tir_t4 = bound_add(total.tir_clone(), tmp2.tir_clone());
      tmp3 = tir_t4;
      total = tmp3.tir_clone();
    }
  }
  if ((((p.c2 !== 0) || (p.c3 !== 0)) || (p.c4 !== 0))) {
    let tmp4 = new Bound();
    const tir_t5 = bound_mul(power.tir_clone(), rise.tir_clone());
    tmp4 = tir_t5;
    power = tmp4.tir_clone();
    if ((p.c2 !== 0)) {
      let tmp5 = new Bound();
      const tir_t6 = bound_mul(tir_new_Bound(true, p.c2), power.tir_clone());
      tmp5 = tir_t6;
      let tmp6 = new Bound();
      const tir_t7 = bound_add(total.tir_clone(), tmp5.tir_clone());
      tmp6 = tir_t7;
      total = tmp6.tir_clone();
    }
  }
  if (((p.c3 !== 0) || (p.c4 !== 0))) {
    let tmp7 = new Bound();
    const tir_t8 = bound_mul(power.tir_clone(), rise.tir_clone());
    tmp7 = tir_t8;
    power = tmp7.tir_clone();
    if ((p.c3 !== 0)) {
      let tmp8 = new Bound();
      const tir_t9 = bound_mul(tir_new_Bound(true, p.c3), power.tir_clone());
      tmp8 = tir_t9;
      let tmp9 = new Bound();
      const tir_t10 = bound_add(total.tir_clone(), tmp8.tir_clone());
      tmp9 = tir_t10;
      total = tmp9.tir_clone();
    }
  }
  if ((p.c4 !== 0)) {
    let tmp10 = new Bound();
    const tir_t11 = bound_mul(power.tir_clone(), rise.tir_clone());
    tmp10 = tir_t11;
    power = tmp10.tir_clone();
    if ((p.c4 !== 0)) {
      let tmp11 = new Bound();
      const tir_t12 = bound_mul(tir_new_Bound(true, p.c4), power.tir_clone());
      tmp11 = tir_t12;
      let tmp12 = new Bound();
      const tir_t13 = bound_add(total.tir_clone(), tmp11.tir_clone());
      tmp12 = tir_t13;
      total = tmp12.tir_clone();
    }
  }
  let growth = new Bound();
  const tir_t14 = bound_pow(p.base, n);
  growth = tir_t14;
  let out = new Bound();
  const tir_t15 = bound_mul(growth.tir_clone(), total.tir_clone());
  out = tir_t15;
  return out.tir_clone();
}

export function posix_end(pat, at) {
  let tmp1 = pat.n;
  let tmp2 = tir_at(pat, at);
  let tmp3 = ((at + 1) >>> 0);
  while ((tmp1 > ((tmp3 + 1) >>> 0))) {
    let tmp4 = tir_at(pat, tmp3);
    if (((tmp4 === 92) && ((tir_at(pat, ((tmp3 + 1) >>> 0)) === 93) || (tir_at(pat, ((tmp3 + 1) >>> 0)) === 92)))) {
      tmp3 = ((tmp3 + 2) >>> 0);
      continue;
    }
    if ((((tmp4 === 91) && (tir_at(pat, ((tmp3 + 1) >>> 0)) === tmp2)) || (tmp4 === 93))) {
      return 4294967295;
    }
    if (((tmp4 === tmp2) && (tir_at(pat, ((tmp3 + 1) >>> 0)) === 93))) {
      return tmp3;
    }
    tmp3 = ((tmp3 + 1) >>> 0);
  }
  return 4294967295;
}

export function posix_item(w, pat, at, stop, base, fold) {
  let tmp1 = ((at + 2) >>> 0);
  let tmp2 = false;
  if ((tir_at(pat, tmp1) === 94)) {
    tmp2 = true;
    tmp1 = ((tmp1 + 1) >>> 0);
  }
  let tmp3 = 255;
  let tmp4 = ((stop - tmp1) >>> 0);
  const tir_t1 = posix_set(pat, tmp1, tmp4);
  tmp3 = tir_t1;
  if ((tmp3 === 255)) {
    w.v.err = 130;
    w.v.erroff = ((stop + 2) >>> 0);
    return;
  }
  if (fold) {
    if (((tmp3 === 11) || (tmp3 === 14))) {
      tmp3 = 5;
    }
  }
  let tmp5 = base;
  set_union(w, tmp5, tmp3, tmp2);
}

export function posix_set(pat, off, nlen) {
  let tmp1 = 0;
  let tmp2 = POSIX.n;
  while ((tmp1 < tmp2)) {
    let tmp3 = ((tir_at(POSIX, tmp1)) >>> 0);
    if ((tmp3 === nlen)) {
      let tmp4 = 0;
      let tmp5 = true;
      while ((tmp4 < tmp3)) {
        if ((tir_at(pat, ((off + tmp4) >>> 0)) !== tir_at(POSIX, ((((tmp1 + 1) >>> 0) + tmp4) >>> 0)))) {
          tmp5 = false;
          break;
        }
        tmp4 = ((tmp4 + 1) >>> 0);
      }
      if (tmp5) {
        return ((tir_at(POSIX, ((((tmp1 + 1) >>> 0) + tmp3) >>> 0))) >>> 0);
      }
    }
    tmp1 = ((((tmp1 + 2) >>> 0) + tmp3) >>> 0);
  }
  return 255;
}

export function price_alt(prices, sibs, first, acc, over) {
  let total = prices.v.n;
  let c = first;
  let k = 0;
  acc.v.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.flow = tir_new_Poly(1, 0, 0, 0, 0, 0);
  while (((k < total) && (c !== 4294967295))) {
    let tmp1 = tir_at(prices.v, c).tir_clone();
    let tmp2 = tir_at(sibs.v, c);
    if ((tmp2 !== 4294967295)) {
      let tmp3 = new Poly();
      const tir_t1 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), tmp1.outs.tir_clone(), over);
      tmp3 = tir_t1;
      let tmp4 = new Poly();
      const tir_t2 = poly_add(acc.v.work.tir_clone(), tmp3.tir_clone(), over);
      tmp4 = tir_t2;
      acc.v.work = tmp4.tir_clone();
      let tmp5 = new Poly();
      const tir_t3 = poly_add(acc.v.stack.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
      tmp5 = tir_t3;
      acc.v.stack = tmp5.tir_clone();
    }
    let tmp6 = new Poly();
    const tir_t4 = poly_add(acc.v.work.tir_clone(), tmp1.work.tir_clone(), over);
    tmp6 = tir_t4;
    acc.v.work = tmp6.tir_clone();
    let tmp7 = new Poly();
    const tir_t5 = poly_add(acc.v.stack.tir_clone(), tmp1.stack.tir_clone(), over);
    tmp7 = tir_t5;
    acc.v.stack = tmp7.tir_clone();
    let tmp8 = new Poly();
    const tir_t6 = poly_add(acc.v.trail.tir_clone(), tmp1.trail.tir_clone(), over);
    tmp8 = tir_t6;
    acc.v.trail = tmp8.tir_clone();
    let tmp9 = new Poly();
    const tir_t7 = poly_add(acc.v.flow.tir_clone(), tmp1.outs.tir_clone(), over);
    tmp9 = tir_t7;
    acc.v.flow = tmp9.tir_clone();
    c = tmp2;
    k = ((k + 1) >>> 0);
  }
  return ArOk;
}

export function price_call(re, whole, cert, over) {
  let novec = tir_cmul(tir_cadd((re.ncap), 1), 2);
  let setup = tir_cmul(tir_cadd((re.nregs), novec), 4);
  let deliver = tir_cmul(novec, 4);
  let reset = tir_cmul((re.nregs), 4);
  let capacity = new Poly();
  let scratch = tir_new_Poly(1, 0, 0, 0, 0, 0);
  let tmp1 = whole.stack.tir_clone();
  capacity = tir_new_Poly(1, 0, 0, 0, 0, 0);
  if ((!(((((tmp1.c0 === 0) && (tmp1.c1 === 0)) && (tmp1.c2 === 0)) && (tmp1.c3 === 0)) && (tmp1.c4 === 0)))) {
    let tmp2 = new Poly();
    const tir_t1 = poly_mul(tmp1.tir_clone(), tir_new_Poly(1, 2, 0, 0, 0, 0), over);
    tmp2 = tir_t1;
    let tmp3 = new Poly();
    const tir_t2 = poly_add(tir_new_Poly(1, 4, 0, 0, 0, 0), tmp2.tir_clone(), over);
    tmp3 = tir_t2;
    capacity = tmp3.tir_clone();
  }
  let tmp4 = new Poly();
  const tir_t3 = poly_mul(capacity.tir_clone(), tir_new_Poly(1, 12, 0, 0, 0, 0), over);
  tmp4 = tir_t3;
  let tmp5 = new Poly();
  const tir_t4 = poly_add(scratch.tir_clone(), tmp4.tir_clone(), over);
  tmp5 = tir_t4;
  scratch = tmp5.tir_clone();
  let tmp6 = whole.trail.tir_clone();
  capacity = tir_new_Poly(1, 0, 0, 0, 0, 0);
  if ((!(((((tmp6.c0 === 0) && (tmp6.c1 === 0)) && (tmp6.c2 === 0)) && (tmp6.c3 === 0)) && (tmp6.c4 === 0)))) {
    let tmp7 = new Poly();
    const tir_t5 = poly_mul(tmp6.tir_clone(), tir_new_Poly(1, 2, 0, 0, 0, 0), over);
    tmp7 = tir_t5;
    let tmp8 = new Poly();
    const tir_t6 = poly_add(tir_new_Poly(1, 4, 0, 0, 0, 0), tmp7.tir_clone(), over);
    tmp8 = tir_t6;
    capacity = tmp8.tir_clone();
  }
  let tmp9 = new Poly();
  const tir_t7 = poly_mul(capacity.tir_clone(), tir_new_Poly(1, 8, 0, 0, 0, 0), over);
  tmp9 = tir_t7;
  let tmp10 = new Poly();
  const tir_t8 = poly_add(scratch.tir_clone(), tmp9.tir_clone(), over);
  tmp10 = tir_t8;
  scratch = tmp10.tir_clone();
  let tmp11 = new Poly();
  const tir_t9 = poly_mul(whole.trail.tir_clone(), tir_new_Poly(1, 4, 0, 0, 0, 0), over);
  tmp11 = tir_t9;
  let tmp12 = new Poly();
  const tir_t10 = poly_add(whole.work.tir_clone(), tmp11.tir_clone(), over);
  tmp12 = tir_t10;
  let tmp13 = new Poly();
  const tir_t11 = poly_add(tir_new_Poly(1, reset, 0, 0, 0, 0), tmp12.tir_clone(), over);
  tmp13 = tir_t11;
  let tmp14 = new Poly();
  const tir_t12 = poly_mul(tmp13.tir_clone(), tir_new_Poly(1, 0, 1, 0, 0, 0), over);
  tmp14 = tir_t12;
  let tmp15 = new Poly();
  const tir_t13 = poly_mul(scratch.tir_clone(), tir_new_Poly(1, 3, 0, 0, 0, 0), over);
  tmp15 = tir_t13;
  let tmp16 = new Poly();
  const tir_t14 = poly_add(tmp14.tir_clone(), tmp15.tir_clone(), over);
  tmp16 = tir_t14;
  let tmp17 = new Poly();
  const tir_t15 = poly_add(tir_new_Poly(1, tir_cadd(setup, deliver), 0, 0, 0, 0), tmp16.tir_clone(), over);
  tmp17 = tir_t15;
  cert.v.cost = tmp17.tir_clone();
  cert.v.stack = whole.stack.tir_clone();
  cert.v.trail = whole.trail.tir_clone();
  let tmp18 = new Poly();
  const tir_t16 = poly_mul(scratch.tir_clone(), tir_new_Poly(1, 2, 0, 0, 0, 0), over);
  tmp18 = tir_t16;
  let tmp19 = new Poly();
  const tir_t17 = poly_add(tir_new_Poly(1, tir_cadd(setup, deliver), 0, 0, 0, 0), tmp18.tir_clone(), over);
  tmp19 = tir_t17;
  cert.v.mem = tmp19.tir_clone();
}

export function price_repeat(code, reps, regions, prices, sibs, at, first, acc, over) {
  let here = tir_at(regions, at).tir_clone();
  let lo = here.lo;
  let hi = here.hi;
  if ((hi <= lo)) {
    return ArShape;
  }
  let verdict = ArOk;
  let head = tir_at(code, lo).tir_clone();
  acc.v.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
  if ((head.op === OpSplit)) {
    const tir_t1 = price_span(code, regions, prices, sibs, ((lo + 1) >>> 0), hi, first, acc, over);
    verdict = tir_t1;
    if ((verdict !== ArOk)) {
      return verdict;
    }
    let tmp1 = new Poly();
    const tir_t2 = poly_add(acc.v.work.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
    tmp1 = tir_t2;
    acc.v.work = tmp1.tir_clone();
    let tmp2 = new Poly();
    const tir_t3 = poly_add(acc.v.stack.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
    tmp2 = tir_t3;
    acc.v.stack = tmp2.tir_clone();
    let tmp3 = new Poly();
    const tir_t4 = poly_add(acc.v.flow.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
    tmp3 = tir_t4;
    acc.v.flow = tmp3.tir_clone();
    return ArOk;
  }
  if ((head.op !== OpRepZero)) {
    return ArShape;
  }
  if ((((hi - lo) >>> 0) < 4)) {
    return ArShape;
  }
  let which = head.arg;
  if ((which >= reps.n)) {
    return ArShape;
  }
  let rep = tir_at(reps, which).tir_clone();
  const tir_t5 = price_span(code, regions, prices, sibs, ((lo + 3) >>> 0), ((hi - 1) >>> 0), first, acc, over);
  verdict = tir_t5;
  if ((verdict !== ArOk)) {
    return verdict;
  }
  let branching = acc.v.flow.tir_clone();
  if ((!(((((branching.base === 1) && (branching.c1 === 0)) && (branching.c2 === 0)) && (branching.c3 === 0)) && (branching.c4 === 0)))) {
    return ArAmbiguous;
  }
  let ways = branching.c0;
  let bounded = (rep.hi !== 4294967295);
  let ceiling = (rep.lo);
  if ((bounded && (ceiling < (rep.hi)))) {
    ceiling = (rep.hi);
  }
  let rounds = tir_new_Poly(1, tir_cadd(ceiling, 1), 0, 0, 0, 0);
  if ((!bounded)) {
    rounds = tir_new_Poly(1, tir_cadd((rep.lo), 1), 1, 0, 0, 0);
  }
  let flow = rounds.tir_clone();
  if ((ways > 1)) {
    let tmp4 = tir_cadd(ceiling, 1);
    if ((!bounded)) {
      tmp4 = tir_cadd((rep.lo), 2);
    }
    let tmp5 = new Bound();
    const tir_t6 = bound_pow(ways, tmp4);
    tmp5 = tir_t6;
    if ((!tmp5.ok)) {
      return ArOverflow;
    }
    flow = tir_new_Poly(1, tmp5.value, 0, 0, 0, 0);
    if ((!bounded)) {
      flow = tir_new_Poly(ways, tmp5.value, 0, 0, 0, 0);
    }
  }
  let body = acc.v.tir_clone();
  let per = tir_new_Poly(1, ways, 0, 0, 0, 0);
  let tmp6 = new Poly();
  const tir_t7 = poly_add(body.work.tir_clone(), per.tir_clone(), over);
  tmp6 = tir_t7;
  let tmp7 = new Poly();
  const tir_t8 = poly_add(tir_new_Poly(1, 2, 0, 0, 0, 0), tmp6.tir_clone(), over);
  tmp7 = tir_t8;
  let tmp8 = new Poly();
  const tir_t9 = poly_mul(flow.tir_clone(), tmp7.tir_clone(), over);
  tmp8 = tir_t9;
  let tmp9 = new Poly();
  const tir_t10 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), tmp8.tir_clone(), over);
  tmp9 = tir_t10;
  acc.v.work = tmp9.tir_clone();
  let tmp10 = new Poly();
  const tir_t11 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), body.stack.tir_clone(), over);
  tmp10 = tir_t11;
  let tmp11 = new Poly();
  const tir_t12 = poly_mul(flow.tir_clone(), tmp10.tir_clone(), over);
  tmp11 = tir_t12;
  acc.v.stack = tmp11.tir_clone();
  let tmp12 = new Poly();
  const tir_t13 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), per.tir_clone(), over);
  tmp12 = tir_t13;
  let leaves = tmp12.tir_clone();
  let tmp13 = new Poly();
  const tir_t14 = poly_add(leaves.tir_clone(), body.trail.tir_clone(), over);
  tmp13 = tir_t14;
  let tmp14 = new Poly();
  const tir_t15 = poly_mul(flow.tir_clone(), tmp13.tir_clone(), over);
  tmp14 = tir_t15;
  let tmp15 = new Poly();
  const tir_t16 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), tmp14.tir_clone(), over);
  tmp15 = tir_t16;
  acc.v.trail = tmp15.tir_clone();
  let tmp16 = new Poly();
  const tir_t17 = poly_mul(flow.tir_clone(), leaves.tir_clone(), over);
  tmp16 = tir_t17;
  acc.v.flow = tmp16.tir_clone();
  return ArOk;
}

export function price_span(code, regions, prices, sibs, lo, hi, first, acc, over) {
  let cursor = first;
  let pc = lo;
  while ((pc < hi)) {
    let tmp1 = cursor;
    if ((tmp1 !== 4294967295)) {
      let tmp2 = tir_at(regions, tmp1).tir_clone();
      if ((tmp2.lo === pc)) {
        if ((tmp2.hi <= pc)) {
          return ArShape;
        }
        let tmp3 = tir_at(prices.v, tmp1).tir_clone();
        let tmp4 = acc.v.flow.tir_clone();
        let tmp5 = new Poly();
        const tir_t1 = poly_mul(tmp4.tir_clone(), tmp3.work.tir_clone(), over);
        tmp5 = tir_t1;
        let tmp6 = new Poly();
        const tir_t2 = poly_add(acc.v.work.tir_clone(), tmp5.tir_clone(), over);
        tmp6 = tir_t2;
        acc.v.work = tmp6.tir_clone();
        let tmp7 = new Poly();
        const tir_t3 = poly_mul(tmp4.tir_clone(), tmp3.stack.tir_clone(), over);
        tmp7 = tir_t3;
        let tmp8 = new Poly();
        const tir_t4 = poly_add(acc.v.stack.tir_clone(), tmp7.tir_clone(), over);
        tmp8 = tir_t4;
        acc.v.stack = tmp8.tir_clone();
        let tmp9 = new Poly();
        const tir_t5 = poly_mul(tmp4.tir_clone(), tmp3.trail.tir_clone(), over);
        tmp9 = tir_t5;
        let tmp10 = new Poly();
        const tir_t6 = poly_add(acc.v.trail.tir_clone(), tmp9.tir_clone(), over);
        tmp10 = tir_t6;
        acc.v.trail = tmp10.tir_clone();
        let tmp11 = new Poly();
        const tir_t7 = poly_mul(tmp4.tir_clone(), tmp3.outs.tir_clone(), over);
        tmp11 = tir_t7;
        acc.v.flow = tmp11.tir_clone();
        pc = tmp2.hi;
        cursor = tir_at(sibs.v, tmp1);
        continue;
      }
    }
    let tmp12 = new Poly();
    const tir_t8 = poly_add(acc.v.work.tir_clone(), acc.v.flow.tir_clone(), over);
    tmp12 = tir_t8;
    const tir_t9 = tir_at(code, pc).op;
    if (tir_t9 === OpChar) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpCharCI) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpClass) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpAny) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpAnyNoNL) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpBsr) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpCirc) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpCircM) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpDoll) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpDollE) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpDollM) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpSod) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpEod) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpEodn) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpWordB) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpNotWordB) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpSave) {
      acc.v.work = tmp12.tir_clone();
      let tmp13 = new Poly();
      const tir_t10 = poly_add(acc.v.trail.tir_clone(), acc.v.flow.tir_clone(), over);
      tmp13 = tir_t10;
      acc.v.trail = tmp13.tir_clone();
    } else if (tir_t9 === OpAccept) {
      acc.v.work = tmp12.tir_clone();
      acc.v.flow = tir_new_Poly(1, 0, 0, 0, 0, 0);
    } else {
      return ArShape;
    }
    pc = ((pc + 1) >>> 0);
  }
  return ArOk;
}

export function push_bt(bt, mem, peak, cost, memlimit, costlimit, stacklimit, pcv, posv, mark) {
  if ((stacklimit <= bt.v.n)) {
    return false;
  }
  let tmp1 = false;
  const tir_t1 = charge_grow(bt.v.a.length, bt.v.n, 12, 178956970, mem, peak, cost, memlimit, costlimit);
  tmp1 = tir_t1;
  if ((!tmp1)) {
    return false;
  }
  tir_push(bt.v, 178956970, tir_mk_obj, tir_new_Bt(pcv, posv, mark));
  return true;
}

export function push_frame(w, capno, nopts, at, unsup) {
  if ((w.v.frames.n > 250)) {
    w.v.err = 119;
    w.v.erroff = ((at + 1) >>> 0);
    return;
  }
  let tmp1 = 0;
  let tmp2 = capno;
  const tir_t1 = alloc_node(w, NdGroup, tmp2, 0, 0);
  tmp1 = tir_t1;
  if ((w.v.err !== 0)) {
    return;
  }
  let tmp3 = 0;
  const tir_t2 = alloc_node(w, NdConcat, 0, 0, 0);
  tmp3 = tir_t2;
  if ((w.v.err !== 0)) {
    return;
  }
  add_child(w, tmp1, tmp3);
  let tmp4 = ((w.v.frames.n - 1) >>> 0);
  let tmp5 = tir_at(w.v.frames, tmp4).cat;
  add_child(w, tmp5, tmp1);
  let tmp6 = w.v.opts;
  let tmp7 = at;
  let tmp8 = unsup;
  tir_push(w.v.frames, 251, tir_mk_obj, tir_new_Frame(tmp1, 0, tmp3, 0, tmp6, tmp7, tmp8));
  w.v.opts = nopts;
}

export function push_job(w, node, here) {
  if ((w.v.jobs.n >= 2048)) {
    w.v.err = 1002;
    return;
  }
  tir_push(w.v.jobs, 2048, tir_mk_obj, tir_new_Job(node, 0, 0, 0, 0, here, 4294967295));
  if ((w.v.peakjobs < w.v.jobs.n)) {
    w.v.peakjobs = w.v.jobs.n;
  }
}

export function push_patch(w, pc) {
  if ((w.v.patches.n >= 4096)) {
    w.v.err = 1002;
    return;
  }
  tir_push(w.v.patches, 4096, tir_mk_u32, pc);
  if ((w.v.peakpatch < w.v.patches.n)) {
    w.v.peakpatch = w.v.patches.n;
  }
}

export function quantifier(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = tir_at(pat, tmp2);
  let tmp4 = 0;
  let tmp5 = 4294967295;
  if ((tmp3 === 43)) {
    tmp4 = 1;
  }
  if ((tmp3 === 63)) {
    tmp5 = 1;
  }
  if ((tmp3 === 123)) {
    let tmp6 = new Quant();
    const tir_t1 = read_braces(pat, tmp2, w);
    tmp6 = tir_t1;
    if ((w.v.err !== 0)) {
      return;
    }
    if ((!tmp6.ok)) {
      let tmp7 = ((tmp3) >>> 0);
      add_char(w, tmp7);
      at.v = ((tmp2 + 1) >>> 0);
      return;
    }
    tmp4 = tmp6.lo;
    tmp5 = tmp6.hi;
    tmp2 = ((tmp6.end - 1) >>> 0);
  }
  tmp2 = ((tmp2 + 1) >>> 0);
  let tmp8 = tmp2;
  const tir_t2 = tir_cell(tmp2);
  skip_gaps(pat, tir_t2, w);
  tmp2 = tir_t2.v;
  let tmp9 = true;
  let tmp10 = false;
  if ((tmp2 < tmp1)) {
    let tmp11 = tir_at(pat, tmp2);
    if ((tmp11 === 63)) {
      tmp9 = false;
      tmp2 = ((tmp2 + 1) >>> 0);
    }
    if ((tmp11 === 43)) {
      tmp10 = true;
      tmp2 = ((tmp2 + 1) >>> 0);
    }
  }
  if ((((w.v.opts & 16) >>> 0) !== 0)) {
    tmp9 = (!tmp9);
  }
  apply_quant(w, tmp4, tmp5, tmp9, tmp8);
  if ((w.v.err !== 0)) {
    return;
  }
  if (tmp10) {
    w.v.err = 1000;
    w.v.erroff = tmp2;
    return;
  }
  at.v = tmp2;
}

export function re_bound(re, kind, mcfg, n) {
  if ((mcfg !== 0)) {
    return tir_new_Answer(3, 0);
  }
  if ((n > 2147483647)) {
    return tir_new_Answer(3, 0);
  }
  let picked = new Cert();
  let ok = false;
  const tir_t1 = tir_cell(picked);
  const tir_t2 = re_pick(re.tir_clone(), tir_t1);
  picked = tir_t1.v;
  ok = tir_t2;
  if ((!ok)) {
    return tir_new_Answer(4, 0);
  }
  let out = new Bound();
  const tir_t3 = cert_bound(picked.tir_clone(), kind, n);
  out = tir_t3;
  if ((!out.ok)) {
    return tir_new_Answer(4, 0);
  }
  return tir_new_Answer(0, out.value);
}

export function re_class(re) {
  let picked = new Cert();
  let ok = false;
  const tir_t1 = tir_cell(picked);
  const tir_t2 = re_pick(re.tir_clone(), tir_t1);
  picked = tir_t1.v;
  ok = tir_t2;
  if ((!ok)) {
    return tir_new_Answer(4, 0);
  }
  let value = 0;
  let known = false;
  const tir_t3 = picked.complexity;
  if (tir_t3 === CcNotProvenLinear) {
    known = true;
  } else if (tir_t3 === CcLinear) {
    value = 1;
    known = true;
  }
  if ((!known)) {
    return tir_new_Answer(4, 0);
  }
  return tir_new_Answer(0, value);
}

export function re_cost(re, mcfg, n) {
  let out = new Answer();
  const tir_t1 = re_bound(re.tir_clone(), BkCost, mcfg, n);
  out = tir_t1;
  return out.tir_clone();
}

export function re_mem(re, mcfg, n) {
  let out = new Answer();
  const tir_t1 = re_bound(re.tir_clone(), BkMem, mcfg, n);
  out = tir_t1;
  return out.tir_clone();
}

export function re_pick(re, picked) {
  if (re.pike) {
    if ((!re.haspikecert)) {
      return false;
    }
    picked.v = re.pikecert.tir_clone();
    return true;
  }
  if ((!re.hascert)) {
    return false;
  }
  picked.v = re.cert.tir_clone();
  return true;
}

export function re_stack(re, mcfg, n) {
  let out = new Answer();
  const tir_t1 = re_bound(re.tir_clone(), BkStack, mcfg, n);
  out = tir_t1;
  return out.tir_clone();
}

export function read_braces(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = ((at + 1) >>> 0);
  let tmp3 = tir_new_Quant(false, 0, 0, 0);
  let tmp4 = false;
  let tmp5 = 0;
  let tmp6 = 4294967295;
  let tmp7 = false;
  let tmp8 = false;
  let tmp9 = 0;
  const tir_t1 = tir_cell(tmp2);
  skip_blanks(pat, tir_t1);
  tmp2 = tir_t1.v;
  while ((tmp2 < tmp1)) {
    const tir_t2 = ct(tir_at(pat, tmp2), 4);
    tmp4 = tir_t2;
    if ((!tmp4)) {
      break;
    }
    tmp7 = true;
    if ((tmp5 <= 65535)) {
      tmp5 = ((((Math.imul(tmp5, 10)) >>> 0) + ((((tir_at(pat, tmp2) - 48) & 255)) >>> 0)) >>> 0);
    }
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  tmp9 = tmp2;
  let tmp10 = tmp2;
  const tir_t3 = tir_cell(tmp2);
  skip_blanks(pat, tir_t3);
  tmp2 = tir_t3.v;
  if (((tmp2 < tmp1) && (tir_at(pat, tmp2) === 44))) {
    tmp2 = ((tmp2 + 1) >>> 0);
    const tir_t4 = tir_cell(tmp2);
    skip_blanks(pat, tir_t4);
    tmp2 = tir_t4.v;
    while ((tmp2 < tmp1)) {
      const tir_t5 = ct(tir_at(pat, tmp2), 4);
      tmp4 = tir_t5;
      if ((!tmp4)) {
        break;
      }
      if ((!tmp8)) {
        tmp6 = 0;
        tmp8 = true;
      }
      if ((tmp6 <= 65535)) {
        tmp6 = ((((Math.imul(tmp6, 10)) >>> 0) + ((((tir_at(pat, tmp2) - 48) & 255)) >>> 0)) >>> 0);
      }
      tmp2 = ((tmp2 + 1) >>> 0);
    }
    tmp9 = tmp2;
    const tir_t6 = tir_cell(tmp2);
    skip_blanks(pat, tir_t6);
    tmp2 = tir_t6.v;
  } else {
    tmp6 = tmp5;
  }
  if ((!(tmp7 || tmp8))) {
    return tmp3.tir_clone();
  }
  if (((tmp2 >= tmp1) || (tir_at(pat, tmp2) !== 125))) {
    return tmp3.tir_clone();
  }
  if ((tmp5 > 65535)) {
    w.v.err = 105;
    w.v.erroff = tmp10;
    return tmp3.tir_clone();
  }
  if ((tmp8 && (tmp6 > 65535))) {
    w.v.err = 105;
    w.v.erroff = tmp9;
    return tmp3.tir_clone();
  }
  if ((tmp6 < tmp5)) {
    w.v.err = 104;
    w.v.erroff = tmp9;
    return tmp3.tir_clone();
  }
  return tir_new_Quant(true, tmp5, tmp6, ((tmp2 + 1) >>> 0));
}

export function read_digit_escape(pat, at, w, incls, c) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = c;
  let tmp4 = tir_new_Esc(EkErr, 0);
  let tmp5 = false;
  if (((!incls) && (tmp3 !== 48))) {
    let tmp6 = ((tmp2 - 1) >>> 0);
    let tmp7 = 0;
    while ((tmp6 < tmp1)) {
      const tir_t1 = ct(tir_at(pat, tmp6), 4);
      tmp5 = tir_t1;
      if ((!tmp5)) {
        break;
      }
      if ((tmp7 <= 65535)) {
        tmp7 = ((((Math.imul(tmp7, 10)) >>> 0) + ((((tir_at(pat, tmp6) - 48) & 255)) >>> 0)) >>> 0);
      }
      tmp6 = ((tmp6 + 1) >>> 0);
    }
    if ((((tmp7 < 10) || (tmp3 >= 56)) || (tmp7 <= w.v.ncap))) {
      if ((tmp7 > 65535)) {
        w.v.err = 161;
        w.v.erroff = tmp6;
        return tmp4.tir_clone();
      }
      note_ref(w, tmp7, tmp6, 0);
      if ((w.v.err !== 0)) {
        return tmp4.tir_clone();
      }
      at.v = tmp6;
      return tir_new_Esc(EkNop, 0);
    }
  }
  if ((tmp3 >= 56)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, ((tmp3) >>> 0));
  }
  let tmp8 = ((((tmp3 - 48) & 255)) >>> 0);
  let tmp9 = 0;
  let tmp10 = false;
  while (((tmp9 < 2) && (tmp2 < tmp1))) {
    const tir_t2 = ct(tir_at(pat, tmp2), 16);
    tmp10 = tir_t2;
    if ((!tmp10)) {
      break;
    }
    tmp8 = ((((Math.imul(tmp8, 8)) >>> 0) + ((((tir_at(pat, tmp2) - 48) & 255)) >>> 0)) >>> 0);
    tmp9 = ((tmp9 + 1) >>> 0);
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  if ((tmp8 > 255)) {
    w.v.err = 151;
    w.v.erroff = tmp2;
    return tmp4.tir_clone();
  }
  at.v = tmp2;
  return tir_new_Esc(EkChar, tmp8);
}

export function read_escape(pat, at, w, incls) {
  let tmp1 = pat.n;
  let tmp2 = ((at.v + 1) >>> 0);
  let tmp3 = tir_new_Esc(EkErr, 0);
  if ((tmp2 >= tmp1)) {
    w.v.err = 101;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  let tmp4 = tir_at(pat, tmp2);
  tmp2 = ((tmp2 + 1) >>> 0);
  if ((tmp4 === 110)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, 10);
  }
  if ((tmp4 === 114)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, 13);
  }
  if ((tmp4 === 116)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, 9);
  }
  if ((tmp4 === 102)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, 12);
  }
  if ((tmp4 === 97)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, 7);
  }
  if ((tmp4 === 101)) {
    at.v = tmp2;
    return tir_new_Esc(EkChar, 27);
  }
  if ((tmp4 === 100)) {
    at.v = tmp2;
    return tir_new_Esc(EkSet, 0);
  }
  if ((tmp4 === 68)) {
    at.v = tmp2;
    return tir_new_Esc(EkNegSet, 0);
  }
  if ((tmp4 === 119)) {
    at.v = tmp2;
    return tir_new_Esc(EkSet, 1);
  }
  if ((tmp4 === 87)) {
    at.v = tmp2;
    return tir_new_Esc(EkNegSet, 1);
  }
  if ((tmp4 === 115)) {
    at.v = tmp2;
    return tir_new_Esc(EkSet, 2);
  }
  if ((tmp4 === 83)) {
    at.v = tmp2;
    return tir_new_Esc(EkNegSet, 2);
  }
  if ((tmp4 === 104)) {
    at.v = tmp2;
    return tir_new_Esc(EkSet, 3);
  }
  if ((tmp4 === 72)) {
    at.v = tmp2;
    return tir_new_Esc(EkNegSet, 3);
  }
  if ((tmp4 === 118)) {
    at.v = tmp2;
    return tir_new_Esc(EkSet, 4);
  }
  if ((tmp4 === 86)) {
    at.v = tmp2;
    return tir_new_Esc(EkNegSet, 4);
  }
  if ((tmp4 === 98)) {
    at.v = tmp2;
    if (incls) {
      return tir_new_Esc(EkChar, 8);
    }
    return tir_new_Esc(EkWordB, 0);
  }
  if ((((((((((tmp4 === 66) || (tmp4 === 65)) || (tmp4 === 90)) || (tmp4 === 122)) || (tmp4 === 82)) || (tmp4 === 71)) || (tmp4 === 75)) || (tmp4 === 88)) || (tmp4 === 67))) {
    if (incls) {
      w.v.err = 107;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    if ((tmp4 === 66)) {
      return tir_new_Esc(EkNotWordB, 0);
    }
    if ((tmp4 === 65)) {
      return tir_new_Esc(EkSod, 0);
    }
    if ((tmp4 === 90)) {
      return tir_new_Esc(EkEodn, 0);
    }
    if ((tmp4 === 122)) {
      return tir_new_Esc(EkEod, 0);
    }
    if ((tmp4 === 82)) {
      return tir_new_Esc(EkBsr, 0);
    }
    w.v.err = 1000;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  if ((tmp4 === 78)) {
    if (incls) {
      w.v.err = 171;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    w.v.err = 1000;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  if ((((((tmp4 === 70) || (tmp4 === 76)) || (tmp4 === 108)) || (tmp4 === 85)) || (tmp4 === 117))) {
    w.v.err = 137;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  if (((tmp4 === 107) || (tmp4 === 103))) {
    if (incls) {
      at.v = tmp2;
      return tir_new_Esc(EkChar, ((tmp4) >>> 0));
    }
    let tmp5 = new Esc();
    const tir_t1 = tir_cell(tmp2);
    const tir_t2 = read_gk(pat, tir_t1, w, (tmp4 === 103));
    tmp2 = tir_t1.v;
    tmp5 = tir_t2;
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    return tmp5.tir_clone();
  }
  if (((tmp4 === 112) || (tmp4 === 80))) {
    read_ucp(pat, tmp2, w);
    return tmp3.tir_clone();
  }
  if ((tmp4 === 99)) {
    if ((tmp2 >= tmp1)) {
      w.v.err = 102;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    let tmp6 = tir_at(pat, tmp2);
    tmp2 = ((tmp2 + 1) >>> 0);
    if (((tmp6 >= 97) && (tmp6 <= 122))) {
      tmp6 = ((tmp6 - 32) & 255);
    }
    if (((tmp6 < 32) || (tmp6 > 126))) {
      w.v.err = 168;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    return tir_new_Esc(EkChar, ((((tmp6 ^ 64) & 255)) >>> 0));
  }
  if ((tmp4 === 120)) {
    const tir_t3 = tir_cell(tmp2);
    const tir_t4 = read_hex(pat, tir_t3, w);
    tmp2 = tir_t3.v;
    tmp3 = tir_t4;
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    return tmp3.tir_clone();
  }
  if ((tmp4 === 111)) {
    const tir_t5 = tir_cell(tmp2);
    const tir_t6 = read_octal_brace(pat, tir_t5, w);
    tmp2 = tir_t5.v;
    tmp3 = tir_t6;
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    return tmp3.tir_clone();
  }
  let tmp7 = false;
  const tir_t7 = ct(tmp4, 4);
  tmp7 = tir_t7;
  if (tmp7) {
    const tir_t8 = tir_cell(tmp2);
    const tir_t9 = read_digit_escape(pat, tir_t8, w, incls, tmp4);
    tmp2 = tir_t8.v;
    tmp3 = tir_t9;
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    return tmp3.tir_clone();
  }
  let tmp8 = false;
  const tir_t10 = ct(tmp4, 32);
  tmp8 = tir_t10;
  if (tmp8) {
    w.v.err = 103;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  at.v = tmp2;
  return tir_new_Esc(EkChar, ((tmp4) >>> 0));
}

export function read_gk(pat, at, w, isg) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = tir_new_Esc(EkErr, 0);
  let tmp4 = tir_new_Esc(EkNop, 0);
  let tmp5 = 0;
  if ((tmp2 < tmp1)) {
    tmp5 = tir_at(pat, tmp2);
  }
  let tmp6 = false;
  let tmp7 = 0;
  if ((!((tmp5 === 123) || ((tmp5 === 60) || (tmp5 === 39))))) {
    if ((!isg)) {
      w.v.err = 169;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    const tir_t1 = ref_number_ahead(pat, tmp2);
    tmp6 = tir_t1;
    if ((!tmp6)) {
      w.v.err = 157;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    const tir_t2 = tir_cell(tmp2);
    const tir_t3 = read_ref_number(pat, tir_t2, w, 4294967295);
    tmp2 = tir_t2.v;
    tmp7 = tir_t3;
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    if ((tmp7 === 0)) {
      w.v.err = 115;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    note_ref(w, tmp7, tmp2, 0);
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    at.v = tmp2;
    return tmp4.tir_clone();
  }
  let tmp8 = 125;
  if ((tmp5 === 60)) {
    tmp8 = 62;
  }
  if ((tmp5 === 39)) {
    tmp8 = 39;
  }
  let tmp9 = (tmp5 === 123);
  let tmp10 = ((tmp2 + 1) >>> 0);
  if (tmp9) {
    const tir_t4 = tir_cell(tmp10);
    skip_blanks(pat, tir_t4);
    tmp10 = tir_t4.v;
  }
  if (isg) {
    const tir_t5 = ref_number_ahead(pat, tmp10);
    tmp6 = tir_t5;
  }
  if (tmp6) {
    const tir_t6 = tir_cell(tmp10);
    const tir_t7 = read_ref_number(pat, tir_t6, w, tmp2);
    tmp10 = tir_t6.v;
    tmp7 = tir_t7;
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    if (tmp9) {
      const tir_t8 = tir_cell(tmp10);
      skip_blanks(pat, tir_t8);
      tmp10 = tir_t8.v;
    }
    if (((tmp10 >= tmp1) || (tir_at(pat, tmp10) !== tmp8))) {
      w.v.err = 219;
      w.v.erroff = tmp10;
      return tmp3.tir_clone();
    }
    tmp10 = ((tmp10 + 1) >>> 0);
    if ((tmp9 && (tmp7 === 0))) {
      w.v.err = 115;
      w.v.erroff = tmp10;
      return tmp3.tir_clone();
    }
    note_ref(w, tmp7, tmp10, 0);
    if ((w.v.err !== 0)) {
      return tmp3.tir_clone();
    }
    at.v = tmp10;
    return tmp4.tir_clone();
  }
  if ((tmp10 >= tmp1)) {
    w.v.err = 162;
    w.v.erroff = tmp10;
    return tmp3.tir_clone();
  }
  let tmp11 = false;
  const tir_t9 = ct(tir_at(pat, tmp10), 4);
  tmp11 = tir_t9;
  if (tmp11) {
    w.v.err = 144;
    w.v.erroff = ((tmp10 + 1) >>> 0);
    return tmp3.tir_clone();
  }
  let tmp12 = tmp10;
  let tmp13 = false;
  while ((tmp10 < tmp1)) {
    const tir_t10 = ct(tir_at(pat, tmp10), 1);
    tmp13 = tir_t10;
    if ((!tmp13)) {
      break;
    }
    tmp10 = ((tmp10 + 1) >>> 0);
  }
  if ((tmp10 === tmp12)) {
    w.v.err = 162;
    w.v.erroff = tmp12;
    return tmp3.tir_clone();
  }
  let tmp14 = ((tmp10 - tmp12) >>> 0);
  if ((tmp14 > 128)) {
    w.v.err = 148;
    w.v.erroff = tmp10;
    return tmp3.tir_clone();
  }
  if (tmp9) {
    const tir_t11 = tir_cell(tmp10);
    skip_blanks(pat, tir_t11);
    tmp10 = tir_t11.v;
  }
  if (((tmp10 >= tmp1) || (tir_at(pat, tmp10) !== tmp8))) {
    w.v.err = 142;
    w.v.erroff = tmp10;
    return tmp3.tir_clone();
  }
  note_ref(w, 4294967295, tmp12, tmp14);
  if ((w.v.err !== 0)) {
    return tmp3.tir_clone();
  }
  at.v = ((tmp10 + 1) >>> 0);
  return tmp4.tir_clone();
}

export function read_hex(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = tir_new_Esc(EkErr, 0);
  let tmp4 = 0;
  let tmp5 = 0;
  let tmp6 = false;
  if (((tmp2 < tmp1) && (tir_at(pat, tmp2) === 123))) {
    tmp2 = ((tmp2 + 1) >>> 0);
    const tir_t1 = tir_cell(tmp2);
    skip_blanks(pat, tir_t1);
    tmp2 = tir_t1.v;
    while ((tmp2 < tmp1)) {
      const tir_t2 = ct(tir_at(pat, tmp2), 8);
      tmp6 = tir_t2;
      if ((!tmp6)) {
        break;
      }
      if ((tmp4 <= 1114111)) {
        let tmp7 = 0;
        const tir_t3 = hex_value(tir_at(pat, tmp2));
        tmp7 = tir_t3;
        tmp4 = ((((Math.imul(tmp4, 16)) >>> 0) + tmp7) >>> 0);
      }
      tmp5 = ((tmp5 + 1) >>> 0);
      tmp2 = ((tmp2 + 1) >>> 0);
    }
    const tir_t4 = tir_cell(tmp2);
    skip_blanks(pat, tir_t4);
    tmp2 = tir_t4.v;
    if (((tmp2 >= tmp1) || (tir_at(pat, tmp2) !== 125))) {
      if (((tmp5 === 0) && (tmp2 >= tmp1))) {
        w.v.err = 178;
        w.v.erroff = tmp2;
        return tmp3.tir_clone();
      }
      w.v.err = 167;
      w.v.erroff = ((tmp2 + 1) >>> 0);
      return tmp3.tir_clone();
    }
    if ((tmp5 === 0)) {
      w.v.err = 178;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    if ((tmp4 > 255)) {
      w.v.err = 134;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    at.v = ((tmp2 + 1) >>> 0);
    return tir_new_Esc(EkChar, tmp4);
  }
  while (((tmp5 < 2) && (tmp2 < tmp1))) {
    const tir_t5 = ct(tir_at(pat, tmp2), 8);
    tmp6 = tir_t5;
    if ((!tmp6)) {
      break;
    }
    let tmp8 = 0;
    const tir_t6 = hex_value(tir_at(pat, tmp2));
    tmp8 = tir_t6;
    tmp4 = ((((Math.imul(tmp4, 16)) >>> 0) + tmp8) >>> 0);
    tmp5 = ((tmp5 + 1) >>> 0);
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  if ((tmp5 === 0)) {
    w.v.err = 178;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  at.v = tmp2;
  return tir_new_Esc(EkChar, tmp4);
}

export function read_octal_brace(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = tir_new_Esc(EkErr, 0);
  if (((tmp2 >= tmp1) || (tir_at(pat, tmp2) !== 123))) {
    w.v.err = 155;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  tmp2 = ((tmp2 + 1) >>> 0);
  const tir_t1 = tir_cell(tmp2);
  skip_blanks(pat, tir_t1);
  tmp2 = tir_t1.v;
  let tmp4 = 0;
  let tmp5 = 0;
  let tmp6 = false;
  while ((tmp2 < tmp1)) {
    const tir_t2 = ct(tir_at(pat, tmp2), 16);
    tmp6 = tir_t2;
    if ((!tmp6)) {
      break;
    }
    if ((tmp4 <= 1114111)) {
      tmp4 = ((((Math.imul(tmp4, 8)) >>> 0) + ((((tir_at(pat, tmp2) - 48) & 255)) >>> 0)) >>> 0);
    }
    tmp5 = ((tmp5 + 1) >>> 0);
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  const tir_t3 = tir_cell(tmp2);
  skip_blanks(pat, tir_t3);
  tmp2 = tir_t3.v;
  if (((tmp2 >= tmp1) || (tir_at(pat, tmp2) !== 125))) {
    if (((tmp5 === 0) && (tmp2 >= tmp1))) {
      w.v.err = 178;
      w.v.erroff = tmp2;
      return tmp3.tir_clone();
    }
    w.v.err = 164;
    w.v.erroff = ((tmp2 + 1) >>> 0);
    return tmp3.tir_clone();
  }
  if ((tmp5 === 0)) {
    w.v.err = 178;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  if ((tmp4 > 255)) {
    w.v.err = 134;
    w.v.erroff = tmp2;
    return tmp3.tir_clone();
  }
  at.v = ((tmp2 + 1) >>> 0);
  return tir_new_Esc(EkChar, tmp4);
}

export function read_ref_number(pat, at, w, valerr) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = (tir_at(pat, tmp2) === 43);
  let tmp4 = (tir_at(pat, tmp2) === 45);
  if ((tmp3 || tmp4)) {
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  let tmp5 = 0;
  let tmp6 = false;
  while ((tmp2 < tmp1)) {
    const tir_t1 = ct(tir_at(pat, tmp2), 4);
    tmp6 = tir_t1;
    if ((!tmp6)) {
      break;
    }
    if ((tmp5 <= 65535)) {
      tmp5 = ((((Math.imul(tmp5, 10)) >>> 0) + ((((tir_at(pat, tmp2) - 48) & 255)) >>> 0)) >>> 0);
    }
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  at.v = tmp2;
  let tmp7 = valerr;
  if ((tmp7 === 4294967295)) {
    tmp7 = tmp2;
  }
  let tmp8 = 65535;
  if (tmp3) {
    tmp8 = ((65535 - w.v.ncap) >>> 0);
  }
  if ((tmp5 > tmp8)) {
    w.v.err = 161;
    w.v.erroff = tmp7;
    return 4294967295;
  }
  if (((tmp3 || tmp4) && (tmp5 === 0))) {
    w.v.err = 126;
    w.v.erroff = tmp7;
    return 4294967295;
  }
  if (tmp4) {
    if ((tmp5 > w.v.ncap)) {
      w.v.err = 115;
      w.v.erroff = tmp7;
      return 4294967295;
    }
    tmp5 = ((((w.v.ncap + 1) >>> 0) - tmp5) >>> 0);
  }
  if (tmp3) {
    tmp5 = ((w.v.ncap + tmp5) >>> 0);
  }
  return tmp5;
}

export function read_ucp(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = at;
  if ((tmp2 >= tmp1)) {
    w.v.err = 146;
    w.v.erroff = tmp2;
    return;
  }
  let tmp3 = tir_at(pat, tmp2);
  tmp2 = ((tmp2 + 1) >>> 0);
  if ((tmp3 === 123)) {
    let tmp4 = false;
    let tmp5 = 0;
    let tmp6 = false;
    while ((tmp2 < tmp1)) {
      let tmp7 = tir_at(pat, tmp2);
      tmp2 = ((tmp2 + 1) >>> 0);
      if ((((tmp7 === 95) || (tmp7 === 45)) || ((tmp7 === 32) || ((tmp7 >= 9) && (tmp7 <= 13))))) {
        continue;
      }
      if ((((tmp5 === 0) && (!tmp4)) && (tmp7 === 94))) {
        tmp4 = true;
        continue;
      }
      if ((tmp7 === 125)) {
        tmp6 = true;
        break;
      }
      if (((tmp7 < 38) || (tmp7 > 122))) {
        w.v.err = 146;
        w.v.erroff = tmp2;
        return;
      }
      tmp5 = ((tmp5 + 1) >>> 0);
      if ((tmp5 >= 49)) {
        break;
      }
    }
    if ((!tmp6)) {
      w.v.err = 146;
      w.v.erroff = tmp2;
      return;
    }
    if ((tmp5 === 0)) {
      w.v.err = 147;
      w.v.erroff = tmp2;
      return;
    }
    w.v.err = 1000;
    w.v.erroff = tmp2;
    return;
  }
  let tmp8 = false;
  const tir_t1 = ct(tmp3, 32);
  tmp8 = tir_t1;
  if ((!tmp8)) {
    w.v.err = 146;
    w.v.erroff = tmp2;
    return;
  }
  w.v.err = 1000;
  w.v.erroff = tmp2;
}

export function ref_number_ahead(pat, at) {
  let tmp1 = pat.n;
  let tmp2 = at;
  let tmp3 = false;
  if ((tmp2 >= tmp1)) {
    return false;
  }
  let tmp4 = tir_at(pat, tmp2);
  if (((tmp4 === 43) || (tmp4 === 45))) {
    if ((tmp1 <= ((tmp2 + 1) >>> 0))) {
      return false;
    }
    const tir_t1 = ct(tir_at(pat, ((tmp2 + 1) >>> 0)), 4);
    tmp3 = tir_t1;
    return tmp3;
  }
  const tir_t2 = ct(tmp4, 4);
  tmp3 = tir_t2;
  return tmp3;
}

export function region_kids(regions, kids, sibs) {
  let total = regions.n;
  let i = 0;
  while ((i < total)) {
    tir_push(kids.v, 8208, tir_mk_u32, 4294967295);
    tir_push(sibs.v, 8208, tir_mk_u32, 4294967295);
    i = ((i + 1) >>> 0);
  }
  i = total;
  while ((i > 1)) {
    i = ((i - 1) >>> 0);
    let tmp1 = tir_at(regions, i).parent;
    const tir_t1 = i;
    tir_bound(sibs.v.n, tir_t1);
    sibs.v.a[tir_t1] = tir_at(kids.v, tmp1);
    const tir_t2 = tmp1;
    tir_bound(kids.v.n, tir_t2);
    kids.v.a[tir_t2] = i;
  }
}

export function sat_add(a, b, over) {
  if ((a > tir_csub(9007199254740991, b))) {
    over.v = true;
    return 9007199254740991;
  }
  return tir_cadd(a, b);
}

export function sat_mul(a, b, over) {
  if (((a === 0) || (b === 0))) {
    return 0;
  }
  if ((a > tir_div_counter(9007199254740991, b, 0))) {
    over.v = true;
    return 9007199254740991;
  }
  return tir_cmul(a, b);
}

export function scan_alt(prices, sibs, first, acc, over) {
  let total = prices.n;
  let c = first;
  let k = 0;
  acc.v.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.flow = tir_new_Poly(1, 0, 0, 0, 0, 0);
  while (((k < total) && (c !== 4294967295))) {
    let tmp1 = tir_at(prices, c).tir_clone();
    let tmp2 = tir_at(sibs.v, c);
    if ((tmp2 !== 4294967295)) {
      let tmp3 = new Poly();
      const tir_t1 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), tmp1.outs.tir_clone(), over);
      tmp3 = tir_t1;
      let tmp4 = new Poly();
      const tir_t2 = poly_add(acc.v.work.tir_clone(), tmp3.tir_clone(), over);
      tmp4 = tir_t2;
      acc.v.work = tmp4.tir_clone();
      let tmp5 = new Poly();
      const tir_t3 = poly_add(acc.v.stack.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
      tmp5 = tir_t3;
      acc.v.stack = tmp5.tir_clone();
    }
    let tmp6 = new Poly();
    const tir_t4 = poly_add(acc.v.work.tir_clone(), tmp1.work.tir_clone(), over);
    tmp6 = tir_t4;
    acc.v.work = tmp6.tir_clone();
    let tmp7 = new Poly();
    const tir_t5 = poly_add(acc.v.stack.tir_clone(), tmp1.stack.tir_clone(), over);
    tmp7 = tir_t5;
    acc.v.stack = tmp7.tir_clone();
    let tmp8 = new Poly();
    const tir_t6 = poly_add(acc.v.trail.tir_clone(), tmp1.trail.tir_clone(), over);
    tmp8 = tir_t6;
    acc.v.trail = tmp8.tir_clone();
    let tmp9 = new Poly();
    const tir_t7 = poly_add(acc.v.flow.tir_clone(), tmp1.outs.tir_clone(), over);
    tmp9 = tir_t7;
    acc.v.flow = tmp9.tir_clone();
    c = tmp2;
    k = ((k + 1) >>> 0);
  }
  return CrOk;
}

export function scan_first(w) {
  let tmp1 = w.v.code.n;
  let tmp2 = 0;
  let tmp3 = (((tmp1 >>> 3) + 1) >>> 0);
  while ((tmp2 < tmp3)) {
    tir_push(w.v.seen, 2147483647, tir_mk_u8, 0);
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  mark_seen(w, 0);
  let tmp4 = 65696;
  while (((w.v.pending.n > 0) && (tmp4 > 0))) {
    tmp4 = tir_csub(tmp4, 1);
    let tmp5 = 0;
    tmp5 = tir_pop(w.v.pending);
    let tmp6 = tir_at(w.v.code, tmp5).tir_clone();
    let tmp7 = tmp6.arg;
    const tir_t1 = tmp6.op;
    if (tir_t1 === OpChar) {
      if ((tmp7 === 13)) {
        w.v.crfirst = 1;
      }
    } else if (tir_t1 === OpCharCI) {
      if ((tmp7 === 13)) {
        w.v.crfirst = 1;
      }
    } else if (tir_t1 === OpClass) {
      let tmp8 = ((((Math.imul(tmp7, 32)) >>> 0) + 1) >>> 0);
      if ((((tir_at(w.v.classes, tmp8) & 32) & 255) !== 0)) {
        w.v.crfirst = 1;
      }
    } else if (tir_t1 === OpSplit) {
      mark_seen(w, tmp7);
      mark_seen(w, tmp6.alt);
    } else if (tir_t1 === OpJump) {
      mark_seen(w, tmp7);
    } else if (tir_t1 === OpRepLoop) {
      let tmp9 = tir_at(w.v.reps, tmp7).tir_clone();
      mark_seen(w, tmp9.body);
      if ((tmp9.lo === 0)) {
        mark_seen(w, tmp9.after);
      }
    } else if (tir_t1 === OpRepNext) {
      let tmp10 = tir_at(w.v.reps, tmp7).tir_clone();
      mark_seen(w, tmp10.head);
      mark_seen(w, tmp10.after);
    } else if (tir_t1 === OpAny) {
      w.v.crfirst = 1;
    } else if (tir_t1 === OpAnyNoNL) {
      w.v.crfirst = 1;
    } else if (tir_t1 === OpBsr) {
      w.v.crfirst = 1;
    } else if (tir_t1 === OpAccept) {
      w.v.crfirst = 1;
    } else if (tir_t1 === OpSave) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpRepZero) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpRepEnter) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpCirc) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpCircM) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpDoll) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpDollE) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpDollM) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpSod) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpEod) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpEodn) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpWordB) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    } else if (tir_t1 === OpNotWordB) {
      mark_seen(w, ((tmp5 + 1) >>> 0));
    }
  }
  if ((tmp4 === 0)) {
    w.v.crfirst = 1;
  }
}

export function scan_repeat(code, reps, regions, prices, sibs, at, first, acc, over) {
  let here = tir_at(regions, at).tir_clone();
  let lo = here.lo;
  let hi = here.hi;
  if ((hi <= lo)) {
    return CrShape;
  }
  let verdict = CrOk;
  let head = tir_at(code, lo).tir_clone();
  acc.v.work = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.stack = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.trail = tir_new_Poly(1, 0, 0, 0, 0, 0);
  acc.v.flow = tir_new_Poly(1, 1, 0, 0, 0, 0);
  if ((head.op === OpSplit)) {
    const tir_t1 = scan_span(code, regions, prices, sibs, ((lo + 1) >>> 0), hi, first, acc, over);
    verdict = tir_t1;
    if ((verdict !== CrOk)) {
      return verdict;
    }
    let tmp1 = new Poly();
    const tir_t2 = poly_add(acc.v.work.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
    tmp1 = tir_t2;
    acc.v.work = tmp1.tir_clone();
    let tmp2 = new Poly();
    const tir_t3 = poly_add(acc.v.stack.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
    tmp2 = tir_t3;
    acc.v.stack = tmp2.tir_clone();
    let tmp3 = new Poly();
    const tir_t4 = poly_add(acc.v.flow.tir_clone(), tir_new_Poly(1, 1, 0, 0, 0, 0), over);
    tmp3 = tir_t4;
    acc.v.flow = tmp3.tir_clone();
    return CrOk;
  }
  if ((head.op !== OpRepZero)) {
    return CrShape;
  }
  if ((((hi - lo) >>> 0) < 4)) {
    return CrShape;
  }
  let which = head.arg;
  if ((which >= reps.n)) {
    return CrShape;
  }
  let rep = tir_at(reps, which).tir_clone();
  const tir_t5 = scan_span(code, regions, prices, sibs, ((lo + 3) >>> 0), ((hi - 1) >>> 0), first, acc, over);
  verdict = tir_t5;
  if ((verdict !== CrOk)) {
    return verdict;
  }
  let branching = acc.v.flow.tir_clone();
  if ((!(((((branching.base === 1) && (branching.c1 === 0)) && (branching.c2 === 0)) && (branching.c3 === 0)) && (branching.c4 === 0)))) {
    return CrAmbiguous;
  }
  let ways = branching.c0;
  let bounded = (rep.hi !== 4294967295);
  let ceiling = (rep.lo);
  if ((bounded && (ceiling < (rep.hi)))) {
    ceiling = (rep.hi);
  }
  let rounds = tir_new_Poly(1, tir_cadd(ceiling, 1), 0, 0, 0, 0);
  if ((!bounded)) {
    rounds = tir_new_Poly(1, tir_cadd((rep.lo), 1), 1, 0, 0, 0);
  }
  let flow = rounds.tir_clone();
  if ((ways > 1)) {
    let tmp4 = tir_cadd(ceiling, 1);
    if ((!bounded)) {
      tmp4 = tir_cadd((rep.lo), 2);
    }
    let tmp5 = new Bound();
    const tir_t6 = bound_pow(ways, tmp4);
    tmp5 = tir_t6;
    if ((!tmp5.ok)) {
      over.v = true;
    }
    flow = tir_new_Poly(1, tmp5.value, 0, 0, 0, 0);
    if ((!bounded)) {
      flow = tir_new_Poly(ways, tmp5.value, 0, 0, 0, 0);
    }
  }
  let body = acc.v.tir_clone();
  let per = tir_new_Poly(1, ways, 0, 0, 0, 0);
  let tmp6 = new Poly();
  const tir_t7 = poly_add(body.work.tir_clone(), per.tir_clone(), over);
  tmp6 = tir_t7;
  let tmp7 = new Poly();
  const tir_t8 = poly_add(tir_new_Poly(1, 2, 0, 0, 0, 0), tmp6.tir_clone(), over);
  tmp7 = tir_t8;
  let tmp8 = new Poly();
  const tir_t9 = poly_mul(flow.tir_clone(), tmp7.tir_clone(), over);
  tmp8 = tir_t9;
  let tmp9 = new Poly();
  const tir_t10 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), tmp8.tir_clone(), over);
  tmp9 = tir_t10;
  acc.v.work = tmp9.tir_clone();
  let tmp10 = new Poly();
  const tir_t11 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), body.stack.tir_clone(), over);
  tmp10 = tir_t11;
  let tmp11 = new Poly();
  const tir_t12 = poly_mul(flow.tir_clone(), tmp10.tir_clone(), over);
  tmp11 = tir_t12;
  acc.v.stack = tmp11.tir_clone();
  let tmp12 = new Poly();
  const tir_t13 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), per.tir_clone(), over);
  tmp12 = tir_t13;
  let leaves = tmp12.tir_clone();
  let tmp13 = new Poly();
  const tir_t14 = poly_add(leaves.tir_clone(), body.trail.tir_clone(), over);
  tmp13 = tir_t14;
  let tmp14 = new Poly();
  const tir_t15 = poly_mul(flow.tir_clone(), tmp13.tir_clone(), over);
  tmp14 = tir_t15;
  let tmp15 = new Poly();
  const tir_t16 = poly_add(tir_new_Poly(1, 1, 0, 0, 0, 0), tmp14.tir_clone(), over);
  tmp15 = tir_t16;
  acc.v.trail = tmp15.tir_clone();
  let tmp16 = new Poly();
  const tir_t17 = poly_mul(flow.tir_clone(), leaves.tir_clone(), over);
  tmp16 = tir_t17;
  acc.v.flow = tmp16.tir_clone();
  return CrOk;
}

export function scan_span(code, regions, prices, sibs, lo, hi, first, acc, over) {
  let cursor = first;
  let pc = lo;
  while ((pc < hi)) {
    let tmp1 = cursor;
    if ((tmp1 !== 4294967295)) {
      let tmp2 = tir_at(regions, tmp1).tir_clone();
      if ((tmp2.lo === pc)) {
        if ((tmp2.hi <= pc)) {
          return CrShape;
        }
        let tmp3 = tir_at(prices, tmp1).tir_clone();
        let tmp4 = acc.v.flow.tir_clone();
        let tmp5 = new Poly();
        const tir_t1 = poly_mul(tmp4.tir_clone(), tmp3.work.tir_clone(), over);
        tmp5 = tir_t1;
        let tmp6 = new Poly();
        const tir_t2 = poly_add(acc.v.work.tir_clone(), tmp5.tir_clone(), over);
        tmp6 = tir_t2;
        acc.v.work = tmp6.tir_clone();
        let tmp7 = new Poly();
        const tir_t3 = poly_mul(tmp4.tir_clone(), tmp3.stack.tir_clone(), over);
        tmp7 = tir_t3;
        let tmp8 = new Poly();
        const tir_t4 = poly_add(acc.v.stack.tir_clone(), tmp7.tir_clone(), over);
        tmp8 = tir_t4;
        acc.v.stack = tmp8.tir_clone();
        let tmp9 = new Poly();
        const tir_t5 = poly_mul(tmp4.tir_clone(), tmp3.trail.tir_clone(), over);
        tmp9 = tir_t5;
        let tmp10 = new Poly();
        const tir_t6 = poly_add(acc.v.trail.tir_clone(), tmp9.tir_clone(), over);
        tmp10 = tir_t6;
        acc.v.trail = tmp10.tir_clone();
        let tmp11 = new Poly();
        const tir_t7 = poly_mul(tmp4.tir_clone(), tmp3.outs.tir_clone(), over);
        tmp11 = tir_t7;
        acc.v.flow = tmp11.tir_clone();
        pc = tmp2.hi;
        cursor = tir_at(sibs.v, tmp1);
        continue;
      }
    }
    let tmp12 = new Poly();
    const tir_t8 = poly_add(acc.v.work.tir_clone(), acc.v.flow.tir_clone(), over);
    tmp12 = tir_t8;
    const tir_t9 = tir_at(code, pc).op;
    if (tir_t9 === OpChar) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpCharCI) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpClass) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpAny) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpAnyNoNL) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpBsr) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpCirc) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpCircM) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpDoll) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpDollE) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpDollM) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpSod) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpEod) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpEodn) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpWordB) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpNotWordB) {
      acc.v.work = tmp12.tir_clone();
    } else if (tir_t9 === OpSave) {
      acc.v.work = tmp12.tir_clone();
      let tmp13 = new Poly();
      const tir_t10 = poly_add(acc.v.trail.tir_clone(), acc.v.flow.tir_clone(), over);
      tmp13 = tir_t10;
      acc.v.trail = tmp13.tir_clone();
    } else if (tir_t9 === OpAccept) {
      acc.v.work = tmp12.tir_clone();
      acc.v.flow = tir_new_Poly(1, 0, 0, 0, 0, 0);
    } else {
      return CrOpcode;
    }
    pc = ((pc + 1) >>> 0);
  }
  return CrOk;
}

export function set_add(w, base, c) {
  let tmp1 = ((base + (((((c) & 255) >>> 3)) >>> 0)) >>> 0);
  let tmp2 = tir_at(BITS, ((c & 7) >>> 0));
  const tir_t1 = tmp1;
  tir_bound(w.v.classes.n, tir_t1);
  w.v.classes.a[tir_t1] = ((tir_at(w.v.classes, tmp1) | tmp2) & 255);
}

export function set_range(w, base, lo, hi, fold) {
  let tmp1 = lo;
  let tmp2 = base;
  while ((tmp1 <= hi)) {
    set_add(w, tmp2, tmp1);
    if (fold) {
      let tmp3 = ((tir_at(FLIP, tmp1)) >>> 0);
      set_add(w, tmp2, tmp3);
    }
    tmp1 = ((tmp1 + 1) >>> 0);
  }
}

export function set_union(w, base, which, neg) {
  let tmp1 = 0;
  let tmp2 = ((Math.imul(which, 32)) >>> 0);
  while ((tmp1 < 32)) {
    let tmp3 = tir_at(SETS, ((tmp2 + tmp1) >>> 0));
    if (neg) {
      tmp3 = ((~tmp3) & 255);
    }
    let tmp4 = ((base + tmp1) >>> 0);
    const tir_t1 = tmp4;
    tir_bound(w.v.classes.n, tir_t1);
    w.v.classes.a[tir_t1] = ((tir_at(w.v.classes, tmp4) | tmp3) & 255);
    tmp1 = ((tmp1 + 1) >>> 0);
  }
}

export function shape_alt(code, regions, sibs, at, first) {
  let here = tir_at(regions, at).tir_clone();
  let hi = here.hi;
  let total = regions.n;
  let p = here.lo;
  let c = first;
  let k = 0;
  while (((k < total) && (c !== 4294967295))) {
    let tmp1 = tir_at(regions, c).tir_clone();
    if ((tmp1.kind !== RkBranch)) {
      return CrChildren;
    }
    let tmp2 = tir_at(sibs.v, c);
    if ((tmp2 !== 4294967295)) {
      if ((p >= hi)) {
        return CrShape;
      }
      let tmp3 = tir_at(code, p).tir_clone();
      if ((tmp3.op !== OpSplit)) {
        return CrShape;
      }
      if ((tmp3.arg !== ((p + 1) >>> 0))) {
        return CrShape;
      }
      if ((tmp1.lo !== ((p + 1) >>> 0))) {
        return CrShape;
      }
      let tmp4 = tmp1.hi;
      if ((tmp4 >= hi)) {
        return CrShape;
      }
      let tmp5 = tir_at(code, tmp4).tir_clone();
      if (((tmp5.op !== OpJump) || (tmp5.arg !== hi))) {
        return CrShape;
      }
      if ((tmp3.alt !== ((tmp4 + 1) >>> 0))) {
        return CrShape;
      }
      p = ((tmp4 + 1) >>> 0);
    } else {
      if (((tmp1.lo !== p) || (tmp1.hi !== hi))) {
        return CrShape;
      }
    }
    c = tmp2;
    k = ((k + 1) >>> 0);
  }
  if ((c !== 4294967295)) {
    return CrChildren;
  }
  if ((k < 2)) {
    return CrShape;
  }
  return CrOk;
}

export function shape_repeat(code, reps, regions, sibs, at, first) {
  let here = tir_at(regions, at).tir_clone();
  let lo = here.lo;
  let hi = here.hi;
  if ((hi <= lo)) {
    return CrShape;
  }
  let head = tir_at(code, lo).tir_clone();
  let body = CrOk;
  if ((head.op === OpSplit)) {
    let tmp1 = ((head.arg === ((lo + 1) >>> 0)) && (head.alt === hi));
    let tmp2 = ((head.arg === hi) && (head.alt === ((lo + 1) >>> 0)));
    if ((!(tmp1 || tmp2))) {
      return CrShape;
    }
    const tir_t1 = shape_span(code, regions, sibs, ((lo + 1) >>> 0), hi, first);
    body = tir_t1;
    return body;
  }
  if ((head.op !== OpRepZero)) {
    return CrShape;
  }
  if ((((hi - lo) >>> 0) < 4)) {
    return CrShape;
  }
  let which = head.arg;
  if ((which >= reps.n)) {
    return CrShape;
  }
  let tmp3 = tir_at(code, ((lo + 1) >>> 0)).tir_clone();
  if (((tmp3.op !== OpRepLoop) || (tmp3.arg !== which))) {
    return CrShape;
  }
  let tmp4 = tir_at(code, ((lo + 2) >>> 0)).tir_clone();
  if (((tmp4.op !== OpRepEnter) || (tmp4.arg !== which))) {
    return CrShape;
  }
  let tail = tir_at(code, ((hi - 1) >>> 0)).tir_clone();
  if (((tail.op !== OpRepNext) || (tail.arg !== which))) {
    return CrShape;
  }
  let rep = tir_at(reps, which).tir_clone();
  if (((rep.head !== ((lo + 1) >>> 0)) || ((rep.body !== ((lo + 2) >>> 0)) || (rep.after !== hi)))) {
    return CrShape;
  }
  const tir_t2 = shape_span(code, regions, sibs, ((lo + 3) >>> 0), ((hi - 1) >>> 0), first);
  body = tir_t2;
  return body;
}

export function shape_span(code, regions, sibs, lo, hi, first) {
  let cursor = first;
  let pc = lo;
  while ((pc < hi)) {
    let tmp1 = cursor;
    if ((tmp1 !== 4294967295)) {
      let tmp2 = tir_at(regions, tmp1).tir_clone();
      if ((tmp2.lo < pc)) {
        return CrShape;
      }
      if ((tmp2.lo === pc)) {
        if (((tmp2.hi <= pc) || (tmp2.hi > hi))) {
          return CrShape;
        }
        pc = tmp2.hi;
        cursor = tir_at(sibs.v, tmp1);
        continue;
      }
    }
    const tir_t1 = tir_at(code, pc).op;
    if (tir_t1 === OpChar) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpCharCI) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpClass) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpAny) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpAnyNoNL) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpBsr) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpCirc) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpCircM) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpDoll) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpDollE) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpDollM) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpSod) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpEod) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpEodn) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpWordB) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpNotWordB) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpSave) {
      pc = ((pc + 1) >>> 0);
    } else if (tir_t1 === OpAccept) {
      pc = ((pc + 1) >>> 0);
    } else {
      return CrOpcode;
    }
  }
  if ((cursor !== 4294967295)) {
    return CrChildren;
  }
  return CrOk;
}

export function size_node(w, at) {
  let tmp1 = at;
  let tmp2 = tir_at(w.v.nodes, tmp1).tir_clone();
  let tmp3 = new Size();
  tmp3.code = 0;
  tmp3.regions = 0;
  tmp3.reps = 0;
  tmp3.visits = 1;
  tmp3.depth = 1;
  tmp3.patches = 0;
  tmp3.nullable = false;
  tmp3.blockers = 0;
  tmp3.needs = false;
  const tir_t1 = tmp2.kind;
  if (tir_t1 === NdNil) {
    tmp3.nullable = true;
  } else if (tir_t1 === NdChar) {
    tmp3.code = 1;
  } else if (tir_t1 === NdCharCI) {
    tmp3.code = 1;
  } else if (tir_t1 === NdClass) {
    tmp3.code = 1;
  } else if (tir_t1 === NdAny) {
    tmp3.code = 1;
  } else if (tir_t1 === NdAnyNoNL) {
    tmp3.code = 1;
  } else if (tir_t1 === NdBsr) {
    tmp3.code = 1;
    tmp3.blockers = 2;
  } else if (tir_t1 === NdCirc) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdCircM) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdDoll) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdDollE) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdDollM) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdSod) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdEod) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdEodn) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdWordB) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdNotWordB) {
    tmp3.code = 1;
    tmp3.nullable = true;
  } else if (tir_t1 === NdConcat) {
    let tmp4 = tmp2.first;
    let tmp5 = 0;
    let tmp6 = 8208;
    tmp3.depth = 0;
    tmp3.nullable = true;
    while (((tmp4 !== 0) && (tmp6 > 0))) {
      tmp6 = tir_csub(tmp6, 1);
      let tmp7 = tir_at(w.v.sizes, tmp4).tir_clone();
      tmp3.code = tir_cadd(tmp3.code, tmp7.code);
      tmp3.regions = tir_cadd(tmp3.regions, tmp7.regions);
      tmp3.reps = tir_cadd(tmp3.reps, tmp7.reps);
      tmp3.visits = tir_cadd(tmp3.visits, tmp7.visits);
      if ((tmp7.depth > tmp3.depth)) {
        tmp3.depth = tmp7.depth;
      }
      let tmp8 = tmp7.patches;
      if ((tmp8 > tmp3.patches)) {
        tmp3.patches = tmp8;
      }
      if ((!tmp7.nullable)) {
        tmp3.nullable = false;
      }
      tmp3.blockers = ((tmp3.blockers | tmp7.blockers) >>> 0);
      if (tmp7.needs) {
        tmp3.needs = true;
      }
      tmp5 = ((tmp5 + 1) >>> 0);
      tmp4 = tir_at(w.v.nodes, tmp4).nxt;
    }
    tmp3.visits = tir_cadd(tmp3.visits, (tmp5));
    tmp3.depth = ((tmp3.depth + 1) >>> 0);
  } else if (tir_t1 === NdAlt) {
    let tmp9 = tmp2.first;
    let tmp10 = 0;
    let tmp11 = 8208;
    tmp3.depth = 0;
    tmp3.nullable = false;
    while (((tmp9 !== 0) && (tmp11 > 0))) {
      tmp11 = tir_csub(tmp11, 1);
      let tmp12 = tir_at(w.v.sizes, tmp9).tir_clone();
      tmp3.code = tir_cadd(tmp3.code, tmp12.code);
      tmp3.regions = tir_cadd(tmp3.regions, tmp12.regions);
      tmp3.reps = tir_cadd(tmp3.reps, tmp12.reps);
      tmp3.visits = tir_cadd(tmp3.visits, tmp12.visits);
      if ((tmp12.depth > tmp3.depth)) {
        tmp3.depth = tmp12.depth;
      }
      let tmp13 = ((tmp10 + tmp12.patches) >>> 0);
      if ((tmp13 > tmp3.patches)) {
        tmp3.patches = tmp13;
      }
      if (tmp12.nullable) {
        tmp3.nullable = true;
      }
      tmp3.blockers = ((tmp3.blockers | tmp12.blockers) >>> 0);
      if (tmp12.needs) {
        tmp3.needs = true;
      }
      tmp10 = ((tmp10 + 1) >>> 0);
      tmp9 = tir_at(w.v.nodes, tmp9).nxt;
    }
    tmp3.visits = tir_cadd(tmp3.visits, (tmp10));
    tmp3.depth = ((tmp3.depth + 1) >>> 0);
    if ((tmp10 > 1)) {
      tmp3.code = tir_cadd(tmp3.code, tir_cmul((((tmp10 - 1) >>> 0)), 2));
      tmp3.regions = tir_cadd(tir_cadd(tmp3.regions, (tmp10)), 1);
    }
  } else if (tir_t1 === NdGroup) {
    let tmp14 = tmp2.first;
    tmp3.nullable = true;
    tmp3.visits = 2;
    if ((tmp14 !== 0)) {
      let tmp15 = tir_at(w.v.sizes, tmp14).tir_clone();
      tmp3.code = tmp15.code;
      tmp3.regions = tmp15.regions;
      tmp3.reps = tmp15.reps;
      tmp3.patches = tmp15.patches;
      tmp3.blockers = tmp15.blockers;
      tmp3.visits = tir_cadd(2, tmp15.visits);
      tmp3.depth = ((1 + tmp15.depth) >>> 0);
      tmp3.nullable = tmp15.nullable;
      tmp3.needs = tmp15.needs;
    }
    if ((tmp2.val !== 0)) {
      tmp3.code = tir_cadd(tmp3.code, 2);
    }
    if ((tmp3.code !== 0)) {
      tmp3.regions = tir_cadd(tmp3.regions, 1);
    }
  } else if (tir_t1 === NdRepeat) {
    let tmp16 = tmp2.first;
    let tmp17 = tir_at(w.v.sizes, tmp16).tir_clone();
    let tmp18 = tmp2.val;
    let tmp19 = tmp2.aux;
    tmp3.nullable = true;
    if ((tmp19 !== 0)) {
      tmp3.depth = ((1 + tmp17.depth) >>> 0);
      tmp3.patches = tmp17.patches;
      tmp3.needs = tmp17.needs;
      tmp3.blockers = tmp17.blockers;
      tmp3.nullable = ((tmp18 === 0) || tmp17.nullable);
      if (((tmp19 === 4294967295) && tmp17.nullable)) {
        tmp3.blockers = ((tmp3.blockers | 1) >>> 0);
      }
      let tmp20 = 1;
      let tmp21 = 0;
      let tmp22 = 0;
      let tmp23 = 0;
      let tmp24 = 2;
      let tmp25 = ((tmp18 === 1) && (tmp19 === 1));
      let tmp26 = ((tmp18 === 0) && (tmp19 === 1));
      let tmp27 = ((tmp18 === 0) && (tmp19 === 4294967295));
      if (tmp26) {
        tmp21 = 1;
        tmp22 = 1;
      }
      if (tmp27) {
        tmp21 = 4;
        tmp22 = 1;
        tmp23 = 1;
      }
      if ((!(tmp25 || (tmp26 || tmp27)))) {
        tmp3.needs = true;
        if ((tmp19 === 4294967295)) {
          tmp20 = tir_cadd((tmp18), 1);
          tmp21 = 4;
          tmp22 = 1;
          tmp23 = 1;
          tmp24 = tir_cadd((tmp18), 3);
        } else {
          tmp20 = (tmp19);
          tmp21 = (((tmp19 - tmp18) >>> 0));
          tmp22 = (((tmp19 - tmp18) >>> 0));
          tmp24 = tir_cadd((tmp19), 2);
        }
      }
      tmp3.code = tir_cadd(tir_cmul(tmp20, tmp17.code), tmp21);
      tmp3.regions = tir_cadd(tir_cmul(tmp20, tmp17.regions), tmp22);
      tmp3.reps = tir_cadd(tir_cmul(tmp20, tmp17.reps), tmp23);
      tmp3.visits = tir_cadd(tmp24, tir_cmul(tmp20, tmp17.visits));
    }
  }
  const tir_t2 = tmp1;
  tir_bound(w.v.sizes.n, tir_t2);
  w.v.sizes.a[tir_t2] = tmp3.tir_clone();
}

export function skip_blanks(pat, at) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  while ((tmp2 < tmp1)) {
    if (((tir_at(pat, tmp2) !== 32) && (tir_at(pat, tmp2) !== 9))) {
      break;
    }
    tmp2 = ((tmp2 + 1) >>> 0);
  }
  at.v = tmp2;
}

export function skip_gaps(pat, at, w) {
  let tmp1 = pat.n;
  let tmp2 = at.v;
  let tmp3 = (((w.v.opts & 8) >>> 0) !== 0);
  let tmp4 = false;
  while ((tmp2 < tmp1)) {
    let tmp5 = tir_at(pat, tmp2);
    if (tmp3) {
      const tir_t1 = ct(tmp5, 2);
      tmp4 = tir_t1;
      if (tmp4) {
        tmp2 = ((tmp2 + 1) >>> 0);
        continue;
      }
      if ((tmp5 === 35)) {
        let tmp6 = ((tmp2 + 1) >>> 0);
        while ((tmp6 < tmp1)) {
          let tmp7 = 0;
          const tir_t2 = newline_at(pat, tmp6, w.v.nltype);
          tmp7 = tir_t2;
          if ((tmp7 !== 0)) {
            tmp6 = ((tmp6 + tmp7) >>> 0);
            break;
          }
          tmp6 = ((tmp6 + 1) >>> 0);
        }
        tmp2 = tmp6;
        continue;
      }
    }
    if ((!((tmp5 === 40) && ((tmp1 > ((tmp2 + 2) >>> 0)) && ((tir_at(pat, ((tmp2 + 1) >>> 0)) === 63) && (tir_at(pat, ((tmp2 + 2) >>> 0)) === 35)))))) {
      break;
    }
    let tmp8 = ((tmp2 + 3) >>> 0);
    while (((tmp8 < tmp1) && (tir_at(pat, tmp8) !== 41))) {
      tmp8 = ((tmp8 + 1) >>> 0);
    }
    if ((tmp8 >= tmp1)) {
      break;
    }
    tmp2 = ((tmp8 + 1) >>> 0);
  }
  at.v = tmp2;
}

export function walk_alt(w, top, job, nd) {
  let tmp1 = top;
  let tmp2 = new Job();
  let tmp3 = 0;
  if ((job.phase === 2)) {
    let tmp4 = w.v.code.n;
    while ((job.base < w.v.patches.n)) {
      let tmp5 = 0;
      tmp5 = tir_pop(w.v.patches);
      const tir_t1 = tmp5;
      tir_bound(w.v.code.n, tir_t1);
      w.v.code.a[tir_t1].arg = tmp4;
    }
    close_region(w, job.arm);
    close_region(w, job.here);
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  if ((job.phase === 3)) {
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  let tmp6 = nd.first;
  if ((job.phase === 0)) {
    const tir_t2 = tmp1;
    tir_bound(w.v.jobs.n, tir_t2);
    w.v.jobs.a[tir_t2].base = w.v.patches.n;
  } else {
    close_region(w, job.arm);
    const tir_t3 = emit(w, OpJump, 0, 0);
    tmp3 = tir_t3;
    push_patch(w, tmp3);
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t4 = job.mark;
    tir_bound(w.v.code.n, tir_t4);
    w.v.code.a[tir_t4].alt = w.v.code.n;
    tmp6 = tir_at(w.v.nodes, job.cur).nxt;
  }
  let tmp7 = (tir_at(w.v.nodes, tmp6).nxt === 0);
  let tmp8 = ((job.phase === 0) && tmp7);
  let tmp9 = job.here;
  if ((!tmp8)) {
    if ((job.phase === 0)) {
      const tir_t5 = open_region(w, RkAlt, job.here);
      tmp9 = tir_t5;
      const tir_t6 = tmp1;
      tir_bound(w.v.jobs.n, tir_t6);
      w.v.jobs.a[tir_t6].here = tmp9;
    }
  }
  if (tmp7) {
    const tir_t7 = tmp1;
    tir_bound(w.v.jobs.n, tir_t7);
    w.v.jobs.a[tir_t7].phase = 2;
    if (tmp8) {
      const tir_t8 = tmp1;
      tir_bound(w.v.jobs.n, tir_t8);
      w.v.jobs.a[tir_t8].phase = 3;
    }
  } else {
    const tir_t9 = emit(w, OpSplit, 0, 0);
    tmp3 = tir_t9;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t10 = tmp3;
    tir_bound(w.v.code.n, tir_t10);
    w.v.code.a[tir_t10].arg = ((tmp3 + 1) >>> 0);
    const tir_t11 = tmp1;
    tir_bound(w.v.jobs.n, tir_t11);
    w.v.jobs.a[tir_t11].mark = tmp3;
    const tir_t12 = tmp1;
    tir_bound(w.v.jobs.n, tir_t12);
    w.v.jobs.a[tir_t12].phase = 1;
  }
  if ((!tmp8)) {
    let tmp10 = 0;
    const tir_t13 = open_region(w, RkBranch, tmp9);
    tmp10 = tir_t13;
    const tir_t14 = tmp1;
    tir_bound(w.v.jobs.n, tir_t14);
    w.v.jobs.a[tir_t14].arm = tmp10;
    tmp9 = tmp10;
  }
  const tir_t15 = tmp1;
  tir_bound(w.v.jobs.n, tir_t15);
  w.v.jobs.a[tir_t15].cur = tmp6;
  push_job(w, tmp6, tmp9);
}

export function walk_lowered(w, top, job, nd) {
  let tmp1 = top;
  let tmp2 = new Job();
  let tmp3 = 0;
  let tmp4 = (nd.opts !== 0);
  let tmp5 = nd.val;
  let tmp6 = nd.aux;
  let tmp7 = nd.first;
  let tmp8 = job.cur;
  if ((tmp8 < tmp5)) {
    const tir_t1 = tmp1;
    tir_bound(w.v.jobs.n, tir_t1);
    w.v.jobs.a[tir_t1].cur = ((tmp8 + 1) >>> 0);
    push_job(w, tmp7, job.here);
    return;
  }
  if ((tmp6 === 4294967295)) {
    let tmp9 = 0;
    const tir_t2 = open_region(w, RkRepeat, job.here);
    tmp9 = tir_t2;
    let tmp10 = 0;
    const tir_t3 = new_rep(w);
    tmp10 = tir_t3;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t4 = tmp1;
    tir_bound(w.v.jobs.n, tir_t4);
    w.v.jobs.a[tir_t4].here = tmp9;
    const tir_t5 = emit(w, OpRepZero, tmp10, 0);
    tmp3 = tir_t5;
    let tmp11 = 0;
    const tir_t6 = emit(w, OpRepLoop, tmp10, 0);
    tmp11 = tir_t6;
    const tir_t7 = emit(w, OpRepEnter, tmp10, 0);
    tmp3 = tir_t7;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t8 = tmp10;
    tir_bound(w.v.reps.n, tir_t8);
    w.v.reps.a[tir_t8].lo = 0;
    const tir_t9 = tmp10;
    tir_bound(w.v.reps.n, tir_t9);
    w.v.reps.a[tir_t9].hi = 4294967295;
    const tir_t10 = tmp10;
    tir_bound(w.v.reps.n, tir_t10);
    w.v.reps.a[tir_t10].greedy = tmp4;
    const tir_t11 = tmp10;
    tir_bound(w.v.reps.n, tir_t11);
    w.v.reps.a[tir_t11].head = tmp11;
    const tir_t12 = tmp10;
    tir_bound(w.v.reps.n, tir_t12);
    w.v.reps.a[tir_t12].body = ((tmp11 + 1) >>> 0);
    const tir_t13 = tmp1;
    tir_bound(w.v.jobs.n, tir_t13);
    w.v.jobs.a[tir_t13].mark = tmp10;
    const tir_t14 = tmp1;
    tir_bound(w.v.jobs.n, tir_t14);
    w.v.jobs.a[tir_t14].phase = 2;
    push_job(w, tmp7, tmp9);
    return;
  }
  if ((tmp8 < tmp6)) {
    let tmp12 = 0;
    const tir_t15 = open_region(w, RkRepeat, job.here);
    tmp12 = tir_t15;
    const tir_t16 = emit(w, OpSplit, 0, 0);
    tmp3 = tir_t16;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t17 = tmp1;
    tir_bound(w.v.jobs.n, tir_t17);
    w.v.jobs.a[tir_t17].here = tmp12;
    const tir_t18 = tmp1;
    tir_bound(w.v.jobs.n, tir_t18);
    w.v.jobs.a[tir_t18].cur = ((tmp8 + 1) >>> 0);
    push_job(w, tmp7, tmp12);
    return;
  }
  let tmp13 = w.v.code.n;
  let tmp14 = job.here;
  let tmp15 = ((tmp6 - tmp5) >>> 0);
  while ((tmp15 > 0)) {
    tmp15 = ((tmp15 - 1) >>> 0);
    let tmp16 = tir_at(w.v.regions, tmp14).lo;
    if (tmp4) {
      const tir_t19 = tmp16;
      tir_bound(w.v.code.n, tir_t19);
      w.v.code.a[tir_t19].arg = ((tmp16 + 1) >>> 0);
      const tir_t20 = tmp16;
      tir_bound(w.v.code.n, tir_t20);
      w.v.code.a[tir_t20].alt = tmp13;
    } else {
      const tir_t21 = tmp16;
      tir_bound(w.v.code.n, tir_t21);
      w.v.code.a[tir_t21].arg = tmp13;
      const tir_t22 = tmp16;
      tir_bound(w.v.code.n, tir_t22);
      w.v.code.a[tir_t22].alt = ((tmp16 + 1) >>> 0);
    }
    close_region(w, tmp14);
    tmp14 = tir_at(w.v.regions, tmp14).parent;
  }
  tmp2 = tir_pop(w.v.jobs);
}

export function walk_repeat(w, top, job, nd) {
  let tmp1 = top;
  let tmp2 = new Job();
  let tmp3 = 0;
  let tmp4 = (nd.opts !== 0);
  if ((job.phase === 1)) {
    let tmp5 = job.mark;
    let tmp6 = w.v.code.n;
    if (tmp4) {
      const tir_t1 = tmp5;
      tir_bound(w.v.code.n, tir_t1);
      w.v.code.a[tir_t1].arg = ((tmp5 + 1) >>> 0);
      const tir_t2 = tmp5;
      tir_bound(w.v.code.n, tir_t2);
      w.v.code.a[tir_t2].alt = tmp6;
    } else {
      const tir_t3 = tmp5;
      tir_bound(w.v.code.n, tir_t3);
      w.v.code.a[tir_t3].arg = tmp6;
      const tir_t4 = tmp5;
      tir_bound(w.v.code.n, tir_t4);
      w.v.code.a[tir_t4].alt = ((tmp5 + 1) >>> 0);
    }
    close_region(w, job.here);
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  if ((job.phase === 2)) {
    let tmp7 = job.mark;
    const tir_t5 = emit(w, OpRepNext, tmp7, 0);
    tmp3 = tir_t5;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t6 = tmp7;
    tir_bound(w.v.reps.n, tir_t6);
    w.v.reps.a[tir_t6].after = w.v.code.n;
    close_region(w, job.here);
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  if ((job.phase === 3)) {
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  if ((job.phase === 4)) {
    walk_lowered(w, tmp1, job.tir_clone(), nd.tir_clone());
    return;
  }
  let tmp8 = nd.val;
  let tmp9 = nd.aux;
  let tmp10 = nd.first;
  if ((tmp9 === 0)) {
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  if (((tmp8 === 1) && (tmp9 === 1))) {
    const tir_t7 = tmp1;
    tir_bound(w.v.jobs.n, tir_t7);
    w.v.jobs.a[tir_t7].phase = 3;
    push_job(w, tmp10, job.here);
    return;
  }
  if ((w.v.lowering && (!(((tmp8 === 0) && (tmp9 === 1)) || ((tmp8 === 0) && (tmp9 === 4294967295)))))) {
    const tir_t8 = tmp1;
    tir_bound(w.v.jobs.n, tir_t8);
    w.v.jobs.a[tir_t8].cur = 0;
    const tir_t9 = tmp1;
    tir_bound(w.v.jobs.n, tir_t9);
    w.v.jobs.a[tir_t9].phase = 4;
    return;
  }
  let tmp11 = 0;
  const tir_t10 = open_region(w, RkRepeat, job.here);
  tmp11 = tir_t10;
  const tir_t11 = tmp1;
  tir_bound(w.v.jobs.n, tir_t11);
  w.v.jobs.a[tir_t11].here = tmp11;
  if (((tmp8 === 0) && (tmp9 === 1))) {
    const tir_t12 = emit(w, OpSplit, 0, 0);
    tmp3 = tir_t12;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t13 = tmp1;
    tir_bound(w.v.jobs.n, tir_t13);
    w.v.jobs.a[tir_t13].mark = tmp3;
    const tir_t14 = tmp1;
    tir_bound(w.v.jobs.n, tir_t14);
    w.v.jobs.a[tir_t14].phase = 1;
    push_job(w, tmp10, tmp11);
    return;
  }
  let tmp12 = 0;
  const tir_t15 = new_rep(w);
  tmp12 = tir_t15;
  if ((w.v.err !== 0)) {
    return;
  }
  const tir_t16 = emit(w, OpRepZero, tmp12, 0);
  tmp3 = tir_t16;
  let tmp13 = 0;
  const tir_t17 = emit(w, OpRepLoop, tmp12, 0);
  tmp13 = tir_t17;
  const tir_t18 = emit(w, OpRepEnter, tmp12, 0);
  tmp3 = tir_t18;
  if ((w.v.err !== 0)) {
    return;
  }
  const tir_t19 = tmp12;
  tir_bound(w.v.reps.n, tir_t19);
  w.v.reps.a[tir_t19].lo = tmp8;
  const tir_t20 = tmp12;
  tir_bound(w.v.reps.n, tir_t20);
  w.v.reps.a[tir_t20].hi = tmp9;
  const tir_t21 = tmp12;
  tir_bound(w.v.reps.n, tir_t21);
  w.v.reps.a[tir_t21].greedy = tmp4;
  const tir_t22 = tmp12;
  tir_bound(w.v.reps.n, tir_t22);
  w.v.reps.a[tir_t22].head = tmp13;
  const tir_t23 = tmp12;
  tir_bound(w.v.reps.n, tir_t23);
  w.v.reps.a[tir_t23].body = ((tmp13 + 1) >>> 0);
  const tir_t24 = tmp1;
  tir_bound(w.v.jobs.n, tir_t24);
  w.v.jobs.a[tir_t24].mark = tmp12;
  const tir_t25 = tmp1;
  tir_bound(w.v.jobs.n, tir_t25);
  w.v.jobs.a[tir_t25].phase = 2;
  push_job(w, tmp10, tmp11);
}

export function word_edge(subj, pos) {
  let tmp1 = subj.n;
  let tmp2 = false;
  let tmp3 = false;
  if ((pos > 0)) {
    const tir_t1 = ct(tir_at(subj, ((pos - 1) >>> 0)), 1);
    tmp2 = tir_t1;
  }
  if ((pos < tmp1)) {
    const tir_t2 = ct(tir_at(subj, pos), 1);
    tmp3 = tir_t2;
  }
  return (tmp2 !== tmp3);
}

export function write_reg(regs, trail, mem, peak, cost, memlimit, costlimit, btlen, slot, value) {
  if ((btlen > 0)) {
    let tmp1 = false;
    const tir_t1 = charge_grow(trail.v.a.length, trail.v.n, 8, 268435455, mem, peak, cost, memlimit, costlimit);
    tmp1 = tir_t1;
    if ((!tmp1)) {
      return false;
    }
    tir_push(trail.v, 268435455, tir_mk_obj, tir_new_Undo(slot, tir_at(regs.v, slot)));
  }
  const tir_t2 = slot;
  tir_bound(regs.v.n, tir_t2);
  regs.v.a[tir_t2] = value;
  return true;
}

// Zero values for every inout parameter type, so the wrapper can
// build what it passes in without knowing how a value is laid out.

export function tir_zero_Work() {
  return new Work();
}

export function tir_zero_vec_u32_512() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_Usage() {
  return new Usage();
}

export function tir_zero_vec_u32_8704() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_vec_Bt_178956970() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function tir_zero_vec_Undo_268435455() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function tir_zero_Cert() {
  return new Cert();
}

export function tir_zero_bool() {
  return false;
}

export function tir_zero_counter() {
  return 0;
}

export function tir_zero_u32() {
  return 0;
}

export function tir_zero_Out() {
  return new Out();
}

export function tir_zero_Ctx() {
  return new Ctx();
}

export function tir_zero_vec_Th_65700() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function tir_zero_vec_Th_131396() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function tir_zero_bytes() {
  return new tir_Seq(tir_EMPTY_U8, 0);
}

export function tir_zero_vec_u32_134549508() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_vec_u32_262796() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_Room() {
  return new Room();
}

export function tir_zero_vec_Price_8208() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function tir_zero_vec_u32_8208() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_Acc() {
  return new Acc();
}
