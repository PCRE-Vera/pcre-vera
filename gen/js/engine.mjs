// Code generated from engine.tir.json. DO NOT EDIT.
//
// Artifact SHA-256:
//   6182089085255ec8c29233aa9a771209a0a4286cd302ddfa9d9ff268e7d7141c
//
// The wave 1 pcre-truste engine as printed from its TIR artifact: the
// pattern parser, the bytecode compiler, and the backtracking matcher. The
// public API is the hand-written wrapper in index.mjs.
//
// The module holds the program and the printer's own tir_ helpers and
// nothing else, which is what lets TIR names be printed verbatim.
//
// A tir_Trap is thrown where TIR-SPEC.md section 12 says a checked operation
// traps. A trap is an engine bug rather than a caller error, so it fails
// loudly instead of reading undefined off the end of a typed array.

/** SHA-256 of the TIR artifact this module was printed from. */
export const artifactSha256 = "6182089085255ec8c29233aa9a771209a0a4286cd302ddfa9d9ff268e7d7141c";

/** What a checked operation throws, per TIR-SPEC.md section 12. */
export class tir_Trap extends Error {
  constructor(code, what) {
    super(`pcretruste: TIR trap ${code}: ${what}`);
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
  }

  tir_clone() {
    const o = new Job();
    o.node = this.node;
    o.phase = this.phase;
    o.cur = this.cur;
    o.mark = this.mark;
    o.base = this.base;
    return o;
  }
}

function tir_new_Job(node, phase, cur, mark, base) {
  const o = new Job();
  o.node = node;
  o.phase = phase;
  o.cur = cur;
  o.mark = mark;
  o.base = base;
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
  }

  tir_clone() {
    const o = new Re();
    o.code = this.code;
    o.classes = this.classes;
    o.reps = this.reps;
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
    return o;
  }
}

function tir_new_Re(code, classes, reps, names, nameents, ncap, nname, nregs, opts, nltype, bsr, hascrlf, crfirst) {
  const o = new Re();
  o.code = code;
  o.classes = classes;
  o.reps = reps;
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
  }
}

function tir_new_Work(nodes, frames, classes, names, nameents, code, reps, jobs, patches, ncap, nname, nclass, nrep, opts, err, erroff, root, refs, hascrlf, crfirst, nltype, clselems, clsrange, clscrlf, pending, seen) {
  const o = new Work();
  o.nodes = nodes;
  o.frames = frames;
  o.classes = classes;
  o.names = names;
  o.nameents = nameents;
  o.code = code;
  o.reps = reps;
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

export function charge_grow(oldcap, lenv, esize, maxv, mem, peak, cost, memlimit, costlimit) {
  if ((lenv < oldcap)) {
    return true;
  }
  if ((lenv >= maxv)) {
    return false;
  }
  let tmp1 = 4;
  if ((((Math.imul(oldcap, 2)) >>> 0) > 4)) {
    tmp1 = ((Math.imul(oldcap, 2)) >>> 0);
  }
  if ((tmp1 > maxv)) {
    tmp1 = maxv;
  }
  let tmp2 = tir_cmul((tmp1), (esize));
  let tmp3 = tir_cmul((oldcap), (esize));
  if ((tmp2 > tir_csub(memlimit, mem.v))) {
    return false;
  }
  let tmp4 = tir_cadd(tmp2, tmp3);
  if ((tmp4 > tir_csub(costlimit, cost.v))) {
    return false;
  }
  cost.v = tir_cadd(cost.v, tmp4);
  let tmp5 = tir_cadd(mem.v, tmp2);
  if ((tmp5 > peak.v)) {
    peak.v = tmp5;
  }
  mem.v = tir_csub(tmp5, tmp3);
  return true;
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
  out.v.re.code = w.code;
  w.code = new tir_Seq(tir_EMPTY_OBJ, 0);
  out.v.re.classes = w.classes;
  w.classes = new tir_Seq(tir_EMPTY_U8, 0);
  out.v.re.reps = w.reps;
  w.reps = new tir_Seq(tir_EMPTY_OBJ, 0);
  out.v.re.names = w.names;
  w.names = new tir_Seq(tir_EMPTY_U8, 0);
  out.v.re.nameents = w.nameents;
  w.nameents = new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function ct(c, bit) {
  return (((tir_at(CTYPE, ((c) >>> 0)) & bit) & 255) !== 0);
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
  let tmp1 = w.v.root;
  push_job(w, tmp1);
  let tmp2 = 65664;
  let tmp3 = 0;
  while ((((w.v.jobs.n > 0) && (tmp2 > 0)) && (w.v.err === 0))) {
    tmp2 = tir_csub(tmp2, 1);
    let tmp4 = ((w.v.jobs.n - 1) >>> 0);
    let tmp5 = tir_at(w.v.jobs, tmp4).tir_clone();
    let tmp6 = tir_at(w.v.nodes, tmp5.node).tir_clone();
    let tmp7 = new Job();
    const tir_t1 = tmp6.kind;
    if (tir_t1 === NdNil) {
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdChar) {
      const tir_t2 = emit(w, OpChar, tmp6.val, 0);
      tmp3 = tir_t2;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdCharCI) {
      const tir_t3 = emit(w, OpCharCI, tmp6.val, 0);
      tmp3 = tir_t3;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdClass) {
      const tir_t4 = emit(w, OpClass, tmp6.val, 0);
      tmp3 = tir_t4;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdAny) {
      const tir_t5 = emit(w, OpAny, tmp6.val, 0);
      tmp3 = tir_t5;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdAnyNoNL) {
      const tir_t6 = emit(w, OpAnyNoNL, tmp6.val, 0);
      tmp3 = tir_t6;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdBsr) {
      const tir_t7 = emit(w, OpBsr, tmp6.val, 0);
      tmp3 = tir_t7;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdCirc) {
      const tir_t8 = emit(w, OpCirc, tmp6.val, 0);
      tmp3 = tir_t8;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdCircM) {
      const tir_t9 = emit(w, OpCircM, tmp6.val, 0);
      tmp3 = tir_t9;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdDoll) {
      const tir_t10 = emit(w, OpDoll, tmp6.val, 0);
      tmp3 = tir_t10;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdDollE) {
      const tir_t11 = emit(w, OpDollE, tmp6.val, 0);
      tmp3 = tir_t11;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdDollM) {
      const tir_t12 = emit(w, OpDollM, tmp6.val, 0);
      tmp3 = tir_t12;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdSod) {
      const tir_t13 = emit(w, OpSod, tmp6.val, 0);
      tmp3 = tir_t13;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdEod) {
      const tir_t14 = emit(w, OpEod, tmp6.val, 0);
      tmp3 = tir_t14;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdEodn) {
      const tir_t15 = emit(w, OpEodn, tmp6.val, 0);
      tmp3 = tir_t15;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdWordB) {
      const tir_t16 = emit(w, OpWordB, tmp6.val, 0);
      tmp3 = tir_t16;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdNotWordB) {
      const tir_t17 = emit(w, OpNotWordB, tmp6.val, 0);
      tmp3 = tir_t17;
      tmp7 = tir_pop(w.v.jobs);
    } else if (tir_t1 === NdConcat) {
      let tmp8 = tmp6.first;
      if ((tmp5.phase !== 0)) {
        tmp8 = tir_at(w.v.nodes, tmp5.cur).nxt;
      }
      if ((tmp8 === 0)) {
        tmp7 = tir_pop(w.v.jobs);
      } else {
        const tir_t18 = tmp4;
        tir_bound(w.v.jobs.n, tir_t18);
        w.v.jobs.a[tir_t18].phase = 1;
        const tir_t19 = tmp4;
        tir_bound(w.v.jobs.n, tir_t19);
        w.v.jobs.a[tir_t19].cur = tmp8;
        push_job(w, tmp8);
      }
    } else if (tir_t1 === NdGroup) {
      if ((tmp5.phase === 0)) {
        if ((tmp6.val !== 0)) {
          let tmp9 = ((Math.imul(tmp6.val, 2)) >>> 0);
          const tir_t20 = emit(w, OpSave, tmp9, 0);
          tmp3 = tir_t20;
        }
        const tir_t21 = tmp4;
        tir_bound(w.v.jobs.n, tir_t21);
        w.v.jobs.a[tir_t21].phase = 1;
        let tmp10 = tmp6.first;
        if ((tmp10 !== 0)) {
          push_job(w, tmp10);
        }
      } else {
        if ((tmp6.val !== 0)) {
          let tmp11 = ((((Math.imul(tmp6.val, 2)) >>> 0) + 1) >>> 0);
          const tir_t22 = emit(w, OpSave, tmp11, 0);
          tmp3 = tir_t22;
        }
        tmp7 = tir_pop(w.v.jobs);
      }
    } else if (tir_t1 === NdAlt) {
      walk_alt(w, tmp4, tmp5.tir_clone(), tmp6.tir_clone());
    } else if (tir_t1 === NdRepeat) {
      walk_repeat(w, tmp4, tmp5.tir_clone(), tmp6.tir_clone());
    }
  }
  if ((w.v.err !== 0)) {
    return;
  }
  if ((tmp2 === 0)) {
    w.v.err = 1003;
    return;
  }
  if (endanchored) {
    const tir_t23 = emit(w, OpEod, 0, 0);
    tmp3 = tir_t23;
  }
  const tir_t24 = emit(w, OpAccept, 0, 0);
  tmp3 = tir_t24;
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

export function match(re, subj, start, mopts, costlimit, stacklimit, memlimit, ov, use) {
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
  let regs = new tir_Seq(tir_EMPTY_U32, 0);
  let bt = new tir_Seq(tir_EMPTY_OBJ, 0);
  let trail = new tir_Seq(tir_EMPTY_OBJ, 0);
  let tmp19 = tir_cmul((((tmp9 + tmp10) >>> 0)), 4);
  if (((tmp19 > memlimit) || (tmp19 > costlimit))) {
    return 2;
  }
  tmp3 = tmp19;
  tmp4 = tmp19;
  tmp2 = tmp19;
  tir_reserve(regs, tmp9, 8704, tir_mk_u32);
  tir_reserve(ov.v, tmp10, 512, tir_mk_u32);
  let tmp20 = 0;
  while ((tmp20 < tmp9)) {
    tir_push(regs, 8704, tir_mk_u32, 4294967295);
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
      tir_bound(regs.n, tir_t1);
      regs.a[tir_t1] = 4294967295;
      tmp26 = ((tmp26 + 1) >>> 0);
    }
    tir_truncate(bt, 0);
    tir_truncate(trail, 0);
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
        let tmp36 = trail.n;
        const tir_t6 = tir_cell(bt);
        const tir_t7 = tir_cell(tmp3);
        const tir_t8 = tir_cell(tmp4);
        const tir_t9 = tir_cell(tmp2);
        const tir_t10 = push_bt(tir_t6, tir_t7, tir_t8, tir_t9, memlimit, costlimit, stacklimit, tmp32.alt, tmp28, tmp36);
        bt = tir_t6.v;
        tmp3 = tir_t7.v;
        tmp4 = tir_t8.v;
        tmp2 = tir_t9.v;
        tmp24 = tir_t10;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        } else {
          if ((tmp5 < bt.n)) {
            tmp5 = bt.n;
          }
        }
        tmp27 = tmp32.arg;
      } else if (tir_t2 === OpJump) {
        tmp27 = tmp32.arg;
      } else if (tir_t2 === OpSave) {
        const tir_t11 = tir_cell(regs);
        const tir_t12 = tir_cell(trail);
        const tir_t13 = tir_cell(tmp3);
        const tir_t14 = tir_cell(tmp4);
        const tir_t15 = tir_cell(tmp2);
        const tir_t16 = write_reg(tir_t11, tir_t12, tir_t13, tir_t14, tir_t15, memlimit, costlimit, bt.n, tmp32.arg, tmp28);
        regs = tir_t11.v;
        trail = tir_t12.v;
        tmp3 = tir_t13.v;
        tmp4 = tir_t14.v;
        tmp2 = tir_t15.v;
        tmp24 = tir_t16;
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
          const tir_t17 = newline_before(subj, tmp28, tmp6);
          tmp38 = tir_t17;
          tmp37 = ((tmp28 !== tmp1) && (tmp38 !== 0));
        }
        if (tmp37) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpDoll) {
        let tmp39 = false;
        const tir_t18 = at_line_end(subj, tmp28, tmp6);
        tmp39 = tir_t18;
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
          const tir_t19 = newline_at(subj, tmp28, tmp6);
          tmp41 = tir_t19;
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
        const tir_t20 = at_line_end(subj, tmp28, tmp6);
        tmp42 = tir_t20;
        if (tmp42) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpWordB) {
        const tir_t21 = word_edge(subj, tmp28);
        tmp24 = tir_t21;
        if (tmp24) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpNotWordB) {
        const tir_t22 = word_edge(subj, tmp28);
        tmp24 = tir_t22;
        if ((!tmp24)) {
          tmp27 = ((tmp27 + 1) >>> 0);
        } else {
          tmp30 = true;
        }
      } else if (tir_t2 === OpRepZero) {
        const tir_t23 = tir_cell(regs);
        const tir_t24 = tir_cell(trail);
        const tir_t25 = tir_cell(tmp3);
        const tir_t26 = tir_cell(tmp4);
        const tir_t27 = tir_cell(tmp2);
        const tir_t28 = write_reg(tir_t23, tir_t24, tir_t25, tir_t26, tir_t27, memlimit, costlimit, bt.n, ((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0), 0);
        regs = tir_t23.v;
        trail = tir_t24.v;
        tmp3 = tir_t25.v;
        tmp4 = tir_t26.v;
        tmp2 = tir_t27.v;
        tmp24 = tir_t28;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        }
        tmp27 = ((tmp27 + 1) >>> 0);
      } else if (tir_t2 === OpRepEnter) {
        const tir_t29 = tir_cell(regs);
        const tir_t30 = tir_cell(trail);
        const tir_t31 = tir_cell(tmp3);
        const tir_t32 = tir_cell(tmp4);
        const tir_t33 = tir_cell(tmp2);
        const tir_t34 = write_reg(tir_t29, tir_t30, tir_t31, tir_t32, tir_t33, memlimit, costlimit, bt.n, ((((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0) + 1) >>> 0), tmp28);
        regs = tir_t29.v;
        trail = tir_t30.v;
        tmp3 = tir_t31.v;
        tmp4 = tir_t32.v;
        tmp2 = tir_t33.v;
        tmp24 = tir_t34;
        if ((!tmp24)) {
          tmp22 = 2;
          tmp23 = false;
          tmp29 = false;
        }
        tmp27 = ((tmp27 + 1) >>> 0);
      } else if (tir_t2 === OpRepLoop) {
        let tmp43 = tir_at(reps, tmp32.arg).tir_clone();
        let tmp44 = tir_at(regs, ((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0));
        if ((tmp44 < tmp43.lo)) {
          tmp27 = tmp43.body;
        } else {
          if ((tmp44 >= tmp43.hi)) {
            tmp27 = tmp43.after;
          } else {
            if (tmp43.greedy) {
              let tmp45 = trail.n;
              const tir_t35 = tir_cell(bt);
              const tir_t36 = tir_cell(tmp3);
              const tir_t37 = tir_cell(tmp4);
              const tir_t38 = tir_cell(tmp2);
              const tir_t39 = push_bt(tir_t35, tir_t36, tir_t37, tir_t38, memlimit, costlimit, stacklimit, tmp43.after, tmp28, tmp45);
              bt = tir_t35.v;
              tmp3 = tir_t36.v;
              tmp4 = tir_t37.v;
              tmp2 = tir_t38.v;
              tmp24 = tir_t39;
              if ((!tmp24)) {
                tmp22 = 2;
                tmp23 = false;
                tmp29 = false;
              } else {
                if ((tmp5 < bt.n)) {
                  tmp5 = bt.n;
                }
              }
              tmp27 = tmp43.body;
            } else {
              let tmp46 = trail.n;
              const tir_t40 = tir_cell(bt);
              const tir_t41 = tir_cell(tmp3);
              const tir_t42 = tir_cell(tmp4);
              const tir_t43 = tir_cell(tmp2);
              const tir_t44 = push_bt(tir_t40, tir_t41, tir_t42, tir_t43, memlimit, costlimit, stacklimit, tmp43.body, tmp28, tmp46);
              bt = tir_t40.v;
              tmp3 = tir_t41.v;
              tmp4 = tir_t42.v;
              tmp2 = tir_t43.v;
              tmp24 = tir_t44;
              if ((!tmp24)) {
                tmp22 = 2;
                tmp23 = false;
                tmp29 = false;
              } else {
                if ((tmp5 < bt.n)) {
                  tmp5 = bt.n;
                }
              }
              tmp27 = tmp43.after;
            }
          }
        }
      } else if (tir_t2 === OpRepNext) {
        let tmp47 = tir_at(reps, tmp32.arg).tir_clone();
        let tmp48 = ((tmp11 + ((Math.imul(tmp32.arg, 2)) >>> 0)) >>> 0);
        let tmp49 = ((tir_at(regs, tmp48) + 1) >>> 0);
        let tmp50 = tir_at(regs, ((tmp48 + 1) >>> 0));
        const tir_t45 = tir_cell(regs);
        const tir_t46 = tir_cell(trail);
        const tir_t47 = tir_cell(tmp3);
        const tir_t48 = tir_cell(tmp4);
        const tir_t49 = tir_cell(tmp2);
        const tir_t50 = write_reg(tir_t45, tir_t46, tir_t47, tir_t48, tir_t49, memlimit, costlimit, bt.n, tmp48, tmp49);
        regs = tir_t45.v;
        trail = tir_t46.v;
        tmp3 = tir_t47.v;
        tmp4 = tir_t48.v;
        tmp2 = tir_t49.v;
        tmp24 = tir_t50;
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
          const tir_t51 = 0;
          tir_bound(regs.n, tir_t51);
          regs.a[tir_t51] = tmp21;
          const tir_t52 = 1;
          tir_bound(regs.n, tir_t52);
          regs.a[tir_t52] = tmp28;
          tmp31 = true;
          tmp29 = false;
        }
      }
      if (tmp30) {
        if ((bt.n === 0)) {
          tmp29 = false;
          tir_truncate(trail, 0);
        } else {
          let tmp53 = new Bt();
          tmp53 = tir_pop(bt);
          tmp27 = tmp53.pc;
          tmp28 = tmp53.pos;
          while ((tmp53.mark < trail.n)) {
            let tmp54 = new Undo();
            tmp54 = tir_pop(trail);
            const tir_t53 = tmp54.slot;
            tir_bound(regs.n, tir_t53);
            regs.a[tir_t53] = tmp54.old;
          }
          if ((bt.n === 0)) {
            tir_truncate(trail, 0);
          }
          tmp30 = false;
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
  use.v.cost = tmp2;
  use.v.stack = tmp5;
  use.v.mem = tmp4;
  if ((tmp22 === 0)) {
    let tmp55 = 0;
    while ((tmp55 < tmp10)) {
      const tir_t54 = tmp55;
      tir_bound(ov.v.n, tir_t54);
      ov.v.a[tir_t54] = tir_at(regs, tmp55);
      tmp55 = ((tmp55 + 1) >>> 0);
    }
  }
  return tmp22;
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

export function push_job(w, node) {
  if ((w.v.jobs.n >= 2048)) {
    w.v.err = 1002;
    return;
  }
  tir_push(w.v.jobs, 2048, tir_mk_obj, tir_new_Job(node, 0, 0, 0, 0));
}

export function push_patch(w, pc) {
  if ((w.v.patches.n >= 4096)) {
    w.v.err = 1002;
    return;
  }
  tir_push(w.v.patches, 4096, tir_mk_u32, pc);
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
  if ((tir_at(w.v.nodes, tmp6).nxt === 0)) {
    const tir_t5 = tmp1;
    tir_bound(w.v.jobs.n, tir_t5);
    w.v.jobs.a[tir_t5].phase = 2;
    if ((job.phase === 0)) {
      const tir_t6 = tmp1;
      tir_bound(w.v.jobs.n, tir_t6);
      w.v.jobs.a[tir_t6].phase = 3;
    }
  } else {
    const tir_t7 = emit(w, OpSplit, 0, 0);
    tmp3 = tir_t7;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t8 = tmp3;
    tir_bound(w.v.code.n, tir_t8);
    w.v.code.a[tir_t8].arg = ((tmp3 + 1) >>> 0);
    const tir_t9 = tmp1;
    tir_bound(w.v.jobs.n, tir_t9);
    w.v.jobs.a[tir_t9].mark = tmp3;
    const tir_t10 = tmp1;
    tir_bound(w.v.jobs.n, tir_t10);
    w.v.jobs.a[tir_t10].phase = 1;
  }
  const tir_t11 = tmp1;
  tir_bound(w.v.jobs.n, tir_t11);
  w.v.jobs.a[tir_t11].cur = tmp6;
  push_job(w, tmp6);
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
    tmp2 = tir_pop(w.v.jobs);
    return;
  }
  if ((job.phase === 3)) {
    tmp2 = tir_pop(w.v.jobs);
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
    push_job(w, tmp10);
    return;
  }
  if (((tmp8 === 0) && (tmp9 === 1))) {
    const tir_t8 = emit(w, OpSplit, 0, 0);
    tmp3 = tir_t8;
    if ((w.v.err !== 0)) {
      return;
    }
    const tir_t9 = tmp1;
    tir_bound(w.v.jobs.n, tir_t9);
    w.v.jobs.a[tir_t9].mark = tmp3;
    const tir_t10 = tmp1;
    tir_bound(w.v.jobs.n, tir_t10);
    w.v.jobs.a[tir_t10].phase = 1;
    push_job(w, tmp10);
    return;
  }
  let tmp11 = 0;
  const tir_t11 = new_rep(w);
  tmp11 = tir_t11;
  if ((w.v.err !== 0)) {
    return;
  }
  const tir_t12 = emit(w, OpRepZero, tmp11, 0);
  tmp3 = tir_t12;
  let tmp12 = 0;
  const tir_t13 = emit(w, OpRepLoop, tmp11, 0);
  tmp12 = tir_t13;
  const tir_t14 = emit(w, OpRepEnter, tmp11, 0);
  tmp3 = tir_t14;
  if ((w.v.err !== 0)) {
    return;
  }
  const tir_t15 = tmp11;
  tir_bound(w.v.reps.n, tir_t15);
  w.v.reps.a[tir_t15].lo = tmp8;
  const tir_t16 = tmp11;
  tir_bound(w.v.reps.n, tir_t16);
  w.v.reps.a[tir_t16].hi = tmp9;
  const tir_t17 = tmp11;
  tir_bound(w.v.reps.n, tir_t17);
  w.v.reps.a[tir_t17].greedy = tmp4;
  const tir_t18 = tmp11;
  tir_bound(w.v.reps.n, tir_t18);
  w.v.reps.a[tir_t18].head = tmp12;
  const tir_t19 = tmp11;
  tir_bound(w.v.reps.n, tir_t19);
  w.v.reps.a[tir_t19].body = ((tmp12 + 1) >>> 0);
  const tir_t20 = tmp1;
  tir_bound(w.v.jobs.n, tir_t20);
  w.v.jobs.a[tir_t20].mark = tmp11;
  const tir_t21 = tmp1;
  tir_bound(w.v.jobs.n, tir_t21);
  w.v.jobs.a[tir_t21].phase = 2;
  push_job(w, tmp10);
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

export function tir_zero_counter() {
  return 0;
}

export function tir_zero_u32() {
  return 0;
}

export function tir_zero_bool() {
  return false;
}

export function tir_zero_Out() {
  return new Out();
}

export function tir_zero_vec_u32_512() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_Usage() {
  return new Usage();
}

export function tir_zero_vec_Bt_178956970() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}

export function tir_zero_vec_u32_8704() {
  return new tir_Seq(tir_EMPTY_U32, 0);
}

export function tir_zero_vec_Undo_268435455() {
  return new tir_Seq(tir_EMPTY_OBJ, 0);
}
