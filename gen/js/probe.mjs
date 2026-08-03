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
// The module holds the program and the printer's own tir_ helpers and
// nothing else, which is what lets TIR names be printed verbatim.
//
// A tir_Trap is thrown where TIR-SPEC.md section 12 says a checked operation
// traps. A trap is an engine bug rather than a caller error, so it fails
// loudly instead of reading undefined off the end of a typed array.

/** SHA-256 of the TIR artifact this module was printed from. */
export const artifactSha256 = "32df7a0b0f41f6b4594832e9eecccc6714817c19d73733de4662bd0b96d2248a";

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

// enum Colour
export const Red = 0;
export const Green = 1;
export const Blue = 2;

export class Nest {
  constructor() {
    this.pair = new Pair();
    this.tag = 0;
  }

  tir_clone() {
    const o = new Nest();
    o.pair = this.pair.tir_clone();
    o.tag = this.tag;
    return o;
  }
}

function tir_new_Nest(pair, tag) {
  const o = new Nest();
  o.pair = pair;
  o.tag = tag;
  return o;
}

export class Pair {
  constructor() {
    this.lo = 0;
    this.hi = 0;
  }

  tir_clone() {
    const o = new Pair();
    o.lo = this.lo;
    o.hi = this.hi;
    return o;
  }
}

function tir_new_Pair(lo, hi) {
  const o = new Pair();
  o.lo = lo;
  o.hi = hi;
  return o;
}

export const BIGB = 200;

export const BIGC = 9007199254740991;

export const BIGI = -2000000009;

export const BIGU = 4000000007;

export const MINI = -2147483648;

export const TABLE = new tir_Seq(new Uint8Array([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]), 16);

export function bump(slot, by) {
  slot.v = ((slot.v + by) >>> 0);
}

export function probe(kind, a, b) {
  let au = ((a) >>> 0);
  let bu = ((b) >>> 0);
  let ai = ((a) | 0);
  let bi = ((b) | 0);
  let a8 = ((a) & 255);
  let b8 = ((b) & 255);
  if ((kind === 0)) {
    return (((Math.imul(au, bu)) >>> 0));
  }
  if ((kind === 1)) {
    return (((au + bu) >>> 0));
  }
  if ((kind === 2)) {
    return (((au - bu) >>> 0));
  }
  if ((kind === 3)) {
    return (((au & bu) >>> 0));
  }
  if ((kind === 4)) {
    return (((au | bu) >>> 0));
  }
  if ((kind === 5)) {
    return (((au ^ bu) >>> 0));
  }
  if ((kind === 6)) {
    return (((-au) >>> 0));
  }
  if ((kind === 7)) {
    return (((~au) >>> 0));
  }
  if ((kind === 8)) {
    return (((au << 17) >>> 0));
  }
  if ((kind === 9)) {
    return ((au >>> 17));
  }
  if ((kind === 10)) {
    return (tir_div_u32(au, bu, 4242));
  }
  if ((kind === 11)) {
    return (tir_rem_u32(au, bu, 4242));
  }
  if ((kind === 12)) {
    return (((((Math.imul(ai, bi)) | 0)) >>> 0));
  }
  if ((kind === 13)) {
    return (((((ai + bi) | 0)) >>> 0));
  }
  if ((kind === 14)) {
    return (((((ai - bi) | 0)) >>> 0));
  }
  if ((kind === 15)) {
    return (((((-ai) | 0)) >>> 0));
  }
  if ((kind === 16)) {
    return ((((ai >> 5)) >>> 0));
  }
  if ((kind === 17)) {
    return (((((ai << 5) | 0)) >>> 0));
  }
  if ((kind === 18)) {
    return (((tir_div_i32(ai, bi, -4242)) >>> 0));
  }
  if ((kind === 19)) {
    return (((tir_rem_i32(ai, bi, -4242)) >>> 0));
  }
  if ((kind === 20)) {
    return (((Math.imul(a8, b8)) & 255));
  }
  if ((kind === 21)) {
    return (((a8 + b8) & 255));
  }
  if ((kind === 22)) {
    return (((a8 - b8) & 255));
  }
  if ((kind === 23)) {
    return (((-a8) & 255));
  }
  if ((kind === 24)) {
    return (((~a8) & 255));
  }
  if ((kind === 25)) {
    return (((a8 << 5) & 255));
  }
  if ((kind === 26)) {
    return ((a8 >>> 3));
  }
  if ((kind === 27)) {
    return tir_cadd(a, b);
  }
  if ((kind === 28)) {
    return tir_csub(a, b);
  }
  if ((kind === 29)) {
    return tir_cmul(a, b);
  }
  if ((kind === 30)) {
    return tir_div_counter(a, b, 4242);
  }
  if ((kind === 31)) {
    return tir_rem_counter(a, b, 4242);
  }
  if ((kind === 32)) {
    return (((a) & 255));
  }
  if ((kind === 33)) {
    return (((a) >>> 0));
  }
  if ((kind === 34)) {
    return (((((a) | 0)) >>> 0));
  }
  if ((kind === 35)) {
    return tir_i32c(ai);
  }
  if ((kind === 36)) {
    return (((ai) & 255));
  }
  if ((kind === 37)) {
    return ((au < bu) ? 1 : 0);
  }
  if ((kind === 38)) {
    let push_bag = new tir_Seq(tir_EMPTY_U32, 0);
    let push_i = 0;
    while ((push_i < au)) {
      tir_push(push_bag, 40, tir_mk_u32, push_i);
      push_i = ((push_i + 1) >>> 0);
    }
    return tir_cadd(tir_cmul((push_bag.a.length), 16777216), (push_bag.n));
  }
  if ((kind === 39)) {
    let res_bag = new tir_Seq(tir_EMPTY_U32, 0);
    tir_reserve(res_bag, bu, 40, tir_mk_u32);
    let res_i = 0;
    while ((res_i < au)) {
      tir_push(res_bag, 40, tir_mk_u32, res_i);
      res_i = ((res_i + 1) >>> 0);
    }
    return tir_cadd(tir_cmul((res_bag.a.length), 16777216), (res_bag.n));
  }
  if ((kind === 40)) {
    let trunc_bag = new tir_Seq(tir_EMPTY_U32, 0);
    let trunc_i = 0;
    while ((trunc_i < au)) {
      tir_push(trunc_bag, 40, tir_mk_u32, trunc_i);
      trunc_i = ((trunc_i + 1) >>> 0);
    }
    tir_truncate(trunc_bag, bu);
    return tir_cadd(tir_cmul((trunc_bag.a.length), 16777216), (trunc_bag.n));
  }
  if ((kind === 41)) {
    let pop_bag = new tir_Seq(tir_EMPTY_U32, 0);
    let pop_i = 0;
    while ((pop_i < au)) {
      tir_push(pop_bag, 40, tir_mk_u32, ((pop_i + 100) >>> 0));
      pop_i = ((pop_i + 1) >>> 0);
    }
    let pop_last = 0;
    pop_last = tir_pop(pop_bag);
    return tir_cadd(tir_cmul((pop_last), 16777216), (pop_bag.n));
  }
  if ((kind === 42)) {
    let copy_from = new tir_Seq(tir_EMPTY_U32, 0);
    tir_push(copy_from, 40, tir_mk_u32, au);
    tir_push(copy_from, 40, tir_mk_u32, bu);
    let copy_to = new tir_Seq(tir_EMPTY_U32, 0);
    copy_to = tir_copy_vec_u32_40(copy_from);
    const tir_t1 = 0;
    tir_bound(copy_from.n, tir_t1);
    copy_from.a[tir_t1] = 777;
    return tir_cadd(tir_cmul((tir_at(copy_to, 0)), 16777216), (copy_to.a.length));
  }
  if ((kind === 43)) {
    let freeze_from = new tir_Seq(tir_EMPTY_U32, 0);
    tir_push(freeze_from, 40, tir_mk_u32, au);
    let freeze_to = new tir_Seq(tir_EMPTY_U32, 0);
    freeze_to = freeze_from;
    freeze_from = new tir_Seq(tir_EMPTY_U32, 0);
    return tir_cadd(tir_cmul((tir_at(freeze_to, 0)), 16777216), (freeze_from.n));
  }
  if ((kind === 44)) {
    return (tir_at(TABLE, ((au & 15) >>> 0)));
  }
  if ((kind === 45)) {
    let sc_bag = new tir_Seq(tir_EMPTY_U32, 0);
    tir_push(sc_bag, 40, tir_mk_u32, 7);
    return (((au < sc_bag.n) && (tir_at(sc_bag, au) === 7)) ? 1 : 0);
  }
  if ((kind === 46)) {
    let sr_first = tir_new_Pair(au, bu);
    let sr_second = sr_first.tir_clone();
    sr_second.lo = 777;
    return tir_cadd(tir_cmul((sr_first.lo), 16777216), (sr_second.lo));
  }
  if ((kind === 47)) {
    let er_bag = new tir_Seq(tir_EMPTY_OBJ, 0);
    tir_push(er_bag, 8, tir_mk_obj, tir_new_Pair(au, bu));
    let er_held = tir_at(er_bag, 0).tir_clone();
    er_held.lo = 777;
    return tir_cadd(tir_cmul((tir_at(er_bag, 0).lo), 16777216), (er_held.lo));
  }
  if ((kind === 48)) {
    let nf_outer = tir_new_Nest(tir_new_Pair(au, bu), 1);
    let nf_held = nf_outer.pair.tir_clone();
    nf_held.lo = 777;
    return tir_cadd(tir_cmul((nf_outer.pair.lo), 16777216), (nf_held.lo));
  }
  if ((kind === 49)) {
    let ew_bag = new tir_Seq(tir_EMPTY_OBJ, 0);
    tir_push(ew_bag, 8, tir_mk_obj, tir_new_Pair(au, bu));
    const tir_t2 = 0;
    tir_bound(ew_bag.n, tir_t2);
    ew_bag.a[tir_t2].lo = 777;
    return tir_cadd(tir_cmul((tir_at(ew_bag, 0).lo), 16777216), (tir_at(ew_bag, 0).hi));
  }
  if ((kind === 50)) {
    let il_held = au;
    const tir_t3 = tir_cell(il_held);
    bump(tir_t3, bu);
    il_held = tir_t3.v;
    return (il_held);
  }
  if ((kind === 51)) {
    let ie_bag = new tir_Seq(tir_EMPTY_U32, 0);
    tir_push(ie_bag, 40, tir_mk_u32, au);
    const tir_t4 = 0;
    tir_bound(ie_bag.n, tir_t4);
    const tir_t5 = tir_cell(ie_bag.a[tir_t4]);
    bump(tir_t5, bu);
    ie_bag.a[tir_t4] = tir_t5.v;
    return (tir_at(ie_bag, 0));
  }
  if ((kind === 52)) {
    let if_held = tir_new_Pair(au, 0);
    const tir_t6 = tir_cell(if_held.lo);
    bump(tir_t6, bu);
    if_held.lo = tir_t6.v;
    return tir_cadd(tir_cmul((if_held.lo), 16777216), (if_held.hi));
  }
  if ((kind === 53)) {
    let is_held = tir_new_Pair(au, bu);
    const tir_t7 = tir_cell(is_held);
    swap_pair(tir_t7);
    is_held = tir_t7.v;
    return tir_cadd(tir_cmul((is_held.lo), 16777216), (is_held.hi));
  }
  if ((kind === 54)) {
    let vb_bag = new tir_Seq(tir_EMPTY_BOOL, 0);
    tir_push(vb_bag, 40, tir_mk_bool, (au < bu));
    tir_push(vb_bag, 40, tir_mk_bool, (au > bu));
    return tir_cadd(tir_cmul(((tir_at(vb_bag, 0) ? 1 : 0)), 16777216), ((tir_at(vb_bag, 1) ? 1 : 0)));
  }
  if ((kind === 55)) {
    let v8_bag = new tir_Seq(tir_EMPTY_U8, 0);
    tir_push(v8_bag, 40, tir_mk_u8, a8);
    tir_push(v8_bag, 40, tir_mk_u8, b8);
    return tir_cadd(tir_cmul((((tir_at(v8_bag, 0)) >>> 0)), 16777216), (((tir_at(v8_bag, 1)) >>> 0)));
  }
  if ((kind === 56)) {
    let vi_bag = new tir_Seq(tir_EMPTY_I32, 0);
    tir_push(vi_bag, 40, tir_mk_i32, ai);
    tir_push(vi_bag, 40, tir_mk_i32, bi);
    return tir_cadd(tir_cmul((((tir_at(vi_bag, 0)) >>> 0)), 16777216), (((tir_at(vi_bag, 1)) >>> 0)));
  }
  if ((kind === 57)) {
    let vc_bag = new tir_Seq(tir_EMPTY_F64, 0);
    tir_push(vc_bag, 40, tir_mk_f64, a);
    tir_push(vc_bag, 40, tir_mk_f64, b);
    return tir_cadd(tir_at(vc_bag, 0), tir_at(vc_bag, 1));
  }
  if ((kind === 58)) {
    let ve_bag = new tir_Seq(tir_EMPTY_I32, 0);
    tir_push(ve_bag, 40, tir_mk_i32, Green);
    tir_push(ve_bag, 40, tir_mk_i32, Blue);
    return tir_cadd(tir_cmul((((tir_at(ve_bag, 0) === Green) ? 1 : 0)), 16777216), (((tir_at(ve_bag, 1) === Blue) ? 1 : 0)));
  }
  if ((kind === 59)) {
    let vf_bag = new tir_Seq(tir_EMPTY_OBJ, 0);
    tir_push(vf_bag, 8, tir_mk_obj, TABLE);
    return tir_cadd(tir_cmul((tir_at(vf_bag, 0).n), 16777216), (((tir_at(tir_at(vf_bag, 0), ((au & 15) >>> 0))) >>> 0)));
  }
  if ((kind === 60)) {
    let sc_picked = Red;
    if ((au === 0)) {
      sc_picked = Red;
    } else {
      if ((au === 1)) {
        sc_picked = Green;
      } else {
        sc_picked = Blue;
      }
    }
    let sc_answer = 0;
    const tir_t8 = sc_picked;
    if (tir_t8 === Red) {
      sc_answer = 10;
    } else if (tir_t8 === Green) {
      sc_answer = 20;
    } else if (tir_t8 === Blue) {
      sc_answer = 30;
    }
    return (sc_answer);
  }
  if ((kind === 61)) {
    let sd_picked = Red;
    if ((au === 1)) {
      sd_picked = Green;
    }
    let sd_answer = 7;
    const tir_t9 = sd_picked;
    if (tir_t9 === Green) {
      // nothing
    } else {
      sd_answer = 99;
    }
    return (sd_answer);
  }
  if ((kind === 62)) {
    let bs_i = 0;
    let bs_total = 0;
    while ((bs_i < 40)) {
      let bs_picked = Red;
      if ((bs_i === au)) {
        bs_picked = Red;
      } else {
        bs_picked = Green;
      }
      const tir_t10 = bs_picked;
      if (tir_t10 === Red) {
        break;
      } else {
        bs_total = ((bs_total + 1) >>> 0);
      }
      bs_i = ((bs_i + 1) >>> 0);
    }
    return tir_cadd(tir_cmul((bs_i), 16777216), (bs_total));
  }
  if ((kind === 63)) {
    let ts_left = au;
    let ts_right = bu;
    const tir_t11 = ts_left;
    ts_left = ts_right;
    ts_right = tir_t11;
    let ts_emptied = 0;
    ts_emptied = ts_left;
    ts_left = 0;
    return tir_cadd(tir_cmul((ts_emptied), 16777216), (ts_left));
  }
  if ((kind === 64)) {
    return (((BIGU + 4000000007) >>> 0));
  }
  if ((kind === 65)) {
    return (((BIGU + BIGU) >>> 0));
  }
  if ((kind === 66)) {
    return (((-BIGU) >>> 0));
  }
  if ((kind === 67)) {
    return (((BIGU << 5) >>> 0));
  }
  if ((kind === 68)) {
    return (((BIGU) & 255));
  }
  if ((kind === 69)) {
    return (((((BIGI + BIGI) | 0)) >>> 0));
  }
  if ((kind === 70)) {
    return (((((-MINI) | 0)) >>> 0));
  }
  if ((kind === 71)) {
    return (((BIGB + BIGB) & 255));
  }
  if ((kind === 72)) {
    return (((BIGC) >>> 0));
  }
  return 0;
}

export function swap_pair(p) {
  let held = p.v.lo;
  p.v.lo = p.v.hi;
  p.v.hi = held;
}

function tir_copy_vec_u32_40(s) {
  const store = tir_mk_u32(s.n);
  for (let i = 0; i < s.n; i++) {
    store[i] = tir_copy_u32(s.a[i]);
  }
  return new tir_Seq(store, s.n);
}

function tir_copy_u32(s) {
  return s;
}

// Zero values for every inout parameter type, so the wrapper can
// build what it passes in without knowing how a value is laid out.

export function tir_zero_u32() {
  return 0;
}

export function tir_zero_Pair() {
  return new Pair();
}
