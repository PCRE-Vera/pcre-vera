// The committed shard of the differential sweep (DESIGN.md section 8), run
// against the generated JavaScript. The same file runs against the Python
// interpreter and the generated Go, so agreeing with it is what "agreeing bit
// for bit" means — and since the Python side has already agreed with pcre2 on
// every one of these cases, agreeing with the file is agreeing with pcre2.
//
// This reaches into the generated module rather than going through the
// wrapper for one reason: the resource half of the sweep is about the `Usage`
// a call reports, which the public API does not return. Asking the generated
// entry points keeps every observed number under test without widening what
// the wrapper promises, and the wrapper stays covered by the conformance and
// accessor runners beside this one.
//
// The three checks of section 8, in the order the record carries them: the
// semantic one is the outcome and the ovector, the cross-matcher one is the
// backtracking matcher on a Pike-eligible program under its own analyzer's
// bounds, and the resource one is the observed usage against the certificate,
// the three limits at the observed value and one below, and a preallocated
// context created at exactly its reservation and one byte under it.

import { strict as assert } from "node:assert";
import test from "node:test";

import { list, load, read, resident, unhex } from "../corpus.mjs";
import {
  BkCost,
  BkMem,
  BkStack,
  Ctx,
  Out,
  Usage,
  bt_match,
  cert_bound,
  compile,
  ctx_create,
  ctx_match,
  match,
  pike_match,
  re_class,
  re_cost,
  re_mem,
  re_stack,
  tir_bytes,
  tir_cell,
  tir_zero_vec_u32_512,
} from "../engine.mjs";

// The committed shard by default, and whatever a campaign wrote when
// PCREVERA_SWEEP names it: a run of `python -m pcrevera.sweep run` writes a
// result document of exactly this shape, so the campaign that closes a
// milestone can be replayed here rather than only in the language that
// produced it.
const CORPUS = process.env.PCREVERA_SWEEP
  ? read(process.env.PCREVERA_SWEEP)
  : load("sweep.json");
const BUDGET = CORPUS.budget;

const MATCHED = 0;
const REFUSED = 2;
const BAD_INPUT = 3;
const EXCEEDS_BUDGET = 4;

// The unset ovector sentinel, which the record spells as -1 the way every
// caller-facing surface does.
const UNSET = 0xffffffff;

// The codes this engine refuses with rather than pcre2's, from
// src/pcrevera/engine/spec.py. Which of them carries an offset is a contract
// rather than a property of the record: a construct or an option outside the
// claimed subset is refused at the byte that asked for it, and a pattern past
// a documented limit is refused about itself. Reading that off the presence of
// a field would mean a record that dropped its offset was replayed as a record
// that never had one.
const UNSUPPORTED = [1000, 1001];
const PATTERN_TOO_LARGE = 1002;

const offsets = (ov) => {
  const out = [];
  for (let i = 0; i < ov.n; i++) {
    out.push(ov.a[i] === UNSET ? -1 : ov.a[i]);
  }
  return out;
};

const usageOf = (use) => ({ cost: use.cost, stack: use.stack, mem: use.mem });

// What to run at: the certificate's own number, never more than the sweep's
// budget. Every runner computes this the same way from the recorded bound, so
// a backend whose accessors disagree runs at different limits and fails on the
// usage rather than passing quietly.
const limitsFor = (bound, budget) => ({
  cost: bound.cost === null ? budget.cost : Math.min(bound.cost, budget.cost),
  stack: bound.stack === null ? budget.stack : Math.min(bound.stack, budget.stack),
  memory: bound.mem === null ? budget.memory : Math.min(bound.mem, budget.memory),
});

// A compile outcome is one of three. "compiled" carries the identity of the
// program; "compileError" is a pcre2 error the engine reproduces; "declined"
// is one of our own codes for a construct outside the claimed subset or a
// pattern past a documented limit, which pcre2 has no opinion about and every
// implementation of this engine still has to refuse identically. A declined
// case carries an offset only where the contract has one.
const refused = (out, one, where) => {
  assert.equal(out.v.err, one.compile.code, `${where}: compile error code`);
  assert.equal(out.v.erroff, one.compile.offset, `${where}: compile error offset`);
};

const compiled = (one, where) => {
  const out = tir_cell(new Out());
  compile(tir_bytes(unhex(one.pattern)), one.flags, one.newline, one.bsr, out);
  // Three kinds and no others: a record whose kind nobody recognizes is a
  // record this runner cannot check, and passing it because its code matched
  // would be reporting a case as replayed when it was not.
  if (one.compile.kind === "compileError") {
    // A pcre2 error is refused at a byte, and the offset is part of it.
    assert.notEqual(one.compile.offset, undefined, `${where}: no compile error offset`);
    refused(out, one, where);
    return null;
  }
  if (one.compile.kind === "declined") {
    if (UNSUPPORTED.includes(one.compile.code)) {
      assert.notEqual(one.compile.offset, undefined, `${where}: no decline offset`);
      refused(out, one, where);
    } else {
      assert.equal(one.compile.code, PATTERN_TOO_LARGE, `${where}: unknown decline code`);
      assert.equal(one.compile.offset, undefined, `${where}: an offset it cannot have`);
      assert.equal(out.v.err, one.compile.code, `${where}: compile error code`);
    }
    return null;
  }
  assert.equal(one.compile.kind, "compiled", `${where}: unknown compile outcome`);
  assert.equal(out.v.err, 0, `${where}: the pattern does not compile`);
  const re = out.v.re;
  assert.equal(re.ncap, one.compile.captures, `${where}: capture count`);
  const names = {};
  for (let i = 0; i < re.nameents.n; i++) {
    const ent = re.nameents.a[i];
    let text = "";
    for (let at = ent.off; at < ent.off + ent.nlen; at++) {
      text += re.names.a[at].toString(16).padStart(2, "0");
    }
    names[text] = ent.grp;
  }
  assert.deepEqual(names, one.compile.names, `${where}: group names`);
  return re;
};

// The analysis the record pins before any subject is tried: which matcher
// compilation selected, which configurations carry a certificate, and the
// complexity class the public accessor answers.
const analysis = (re, one, where) => {
  assert.equal(re.pike, one.pike, `${where}: pike eligibility`);
  assert.equal(re.hascert, one.cert.backtrack, `${where}: backtracking certificate`);
  assert.equal(re.haspikecert, one.cert.pike, `${where}: pike certificate`);
  const held = re_class(re);
  if (one.class === null) {
    assert.equal(held.status, EXCEEDS_BUDGET, `${where}: the class accessor`);
  } else {
    assert.equal(held.status, 0, `${where}: the class accessor`);
    assert.equal(held.value, one.class, `${where}: the class accessor`);
  }
};

const accessors = (re, n, bound, where) => {
  for (const [name, answered] of [
    ["cost", re_cost(re, 0, n)],
    ["stack", re_stack(re, 0, n)],
    ["mem", re_mem(re, 0, n)],
  ]) {
    const want = bound[name];
    if (want === null) {
      assert.equal(answered.status, EXCEEDS_BUDGET, `${where}: the ${name} accessor at n=${n}`);
      continue;
    }
    assert.equal(answered.status, 0, `${where}: the ${name} accessor at n=${n}`);
    assert.equal(answered.value, want, `${where}: the ${name} accessor at n=${n}`);
  }
};

// One call, on the selected path or on the backtracking one. The two entry
// points mean the same thing and differ in one argument — only the public one
// takes the match configuration — so each gets a wrapper of its own and
// everything below is handed whichever it should ask.
const answered = (status, ov, use) => ({
  status,
  ovector: offsets(ov.v),
  usage: usageOf(use.v),
});

const scratch = () => [tir_cell(tir_zero_vec_u32_512()), tir_cell(new Usage())];

const ranSelected = (re, subject, trial, limits) => {
  const [ov, use] = scratch();
  const status = match(
    re, tir_bytes(subject), trial.start, trial.matchFlags, 0,
    limits.cost, limits.stack, limits.memory, ov, use,
  );
  return answered(status, ov, use);
};

const ranBacktracking = (re, subject, trial, limits) => {
  const [ov, use] = scratch();
  const status = bt_match(
    re, tir_bytes(subject), trial.start, trial.matchFlags,
    limits.cost, limits.stack, limits.memory, ov, use,
  );
  return answered(status, ov, use);
};

const ranPike = (re, subject, trial, limits) => {
  const [ov, use] = scratch();
  const status = pike_match(
    re, tir_bytes(subject), trial.start, trial.matchFlags,
    limits.cost, limits.stack, limits.memory, ov, use,
  );
  return answered(status, ov, use);
};

// Each limit at the observed value and one below it: the deterministic budget
// boundary of DESIGN.md section 8. At the observed value the run gives exactly
// the answer it just gave; one unit below, it is refused. A dimension whose
// observed value is zero has no "one below" to ask about.
const edges = (run, re, subject, trial, used, limits, got, where) => {
  for (const [name, field] of [
    ["cost", "cost"],
    ["stack", "stack"],
    ["mem", "memory"],
  ]) {
    const observed = used[name];
    const again = run(re, subject, trial, { ...limits, [field]: observed });
    assert.equal(again.status, got.status, `${where}: at the observed ${name} limit ${observed}`);
    assert.deepEqual(
      again.ovector,
      got.ovector,
      `${where}: at the observed ${name} limit ${observed}`,
    );
    if (observed === 0) {
      continue;
    }
    const refused = run(re, subject, trial, { ...limits, [field]: observed - 1 });
    assert.equal(
      refused.status,
      REFUSED,
      `${where}: one below the observed ${name} limit ${observed}`,
    );
  }
};

// The other matcher on the same trial, under its own analyzer's bounds. The
// selected path on a Pike-eligible program is the Pike VM, so what this adds
// is the backtracking run; where the backtracking analyzer has no finite
// certificate the record says so and there is no agreement to be had.
const crossMatcher = (re, subject, trial, where, budget) => {
  const bound = { cost: null, stack: null, mem: null };
  if (re.hascert) {
    for (const [name, kind] of [
      ["cost", BkCost],
      ["stack", BkStack],
      ["mem", BkMem],
    ]) {
      const held = cert_bound(re.cert, kind, subject.length);
      bound[name] = held.ok ? held.value : null;
    }
  }
  // The backtracking bound is checked here rather than through the accessors,
  // which answer for the selected path only. A backend whose backtracking
  // analyzer drifted would otherwise be caught only where the drift moved an
  // outcome, and under limits both the old and the new bound allow it would
  // not.
  assert.deepEqual(bound, trial.cross.bound, `${where}: the backtracking bound`);
  const limits = limitsFor(bound, budget);
  const got = ranBacktracking(re, subject, trial, limits);
  assert.equal(got.status, trial.cross.outcome, `${where}: the backtracking outcome`);
  if (trial.cross.outcome === MATCHED) {
    assert.deepEqual(got.ovector, trial.cross.ovector, `${where}: the backtracking ovector`);
  }
  assert.deepEqual(got.usage, trial.cross.usage, `${where}: the backtracking usage`);
  if (trial.cross.edges) {
    edges(ranBacktracking, re, subject, trial, trial.cross.usage, limits, got, `${where} backtracking`);
  }
};

const oneTrial = (re, one, at, where, budget) => {
  const trial = one.trials[at];
  const subject = unhex(trial.subject);
  accessors(re, subject.length, trial.bound, where);
  const limits = limitsFor(trial.bound, budget);
  const got = ranSelected(re, subject, trial, limits);
  assert.equal(got.status, trial.outcome, `${where}: outcome`);
  if (trial.outcome === MATCHED) {
    assert.deepEqual(got.ovector, trial.ovector, `${where}: ovector`);
  }
  assert.deepEqual(got.usage, trial.usage, `${where}: usage`);
  if (trial.edges) {
    edges(ranSelected, re, subject, trial, trial.usage, limits, got, where);
  }
  if (trial.cross !== undefined) {
    crossMatcher(re, subject, trial, where, budget);
  }
};

// The Pike VM says no to a program compilation did not route to it. There is
// no pair to compare on an ineligible pattern, and the refusal is what is
// worth pinning instead.
const ineligible = (re, where, budget) => {
  const got = ranPike(re, new Uint8Array(0), { start: 0, matchFlags: 0 }, budget);
  assert.equal(got.status, BAD_INPUT, `${where}: the Pike VM on an ineligible program`);
};

// Creation charges one cost unit per IR byte it zeroes, so a cost ceiling
// equal to the memory one can never be the limit that binds: what a refusal
// here is about is always the size of the reservation.
const created = (re, one, memory, budget) => {
  const held = tir_cell(new Ctx());
  const status = ctx_create(re, 0, one.maxlen, budget.memory, budget.stack, memory, held);
  return { status, held };
};

const context = (re, one, where, budget) => {
  const { status, held } = created(re, one, budget.memory, budget);
  assert.equal(status, one.context.status, `${where}: creation`);
  if (status !== 0) {
    return;
  }
  assert.equal(held.v.memcap, one.context.memcap, `${where}: the reservation`);
  assert.equal(resident(held.v, re), held.v.memcap, `${where}: the bytes really held`);
  assert.equal(
    created(re, one, one.context.memcap, budget).status,
    0,
    `${where}: creation at the edge`,
  );
  assert.equal(
    created(re, one, one.context.memcap - 1, budget).status,
    REFUSED,
    `${where}: creation one byte below`,
  );

  const ov = tir_cell(tir_zero_vec_u32_512());
  const use = tir_cell(new Usage());
  one.context.calls.forEach((call, at) => {
    const trial = one.trials[at];
    const got = ctx_match(
      held,
      tir_bytes(unhex(trial.subject)),
      trial.start,
      trial.matchFlags,
      budget.memory,
      budget.stack,
      ov,
      use,
    );
    assert.equal(got, call.outcome, `${where}: context call ${at}`);
    assert.deepEqual(usageOf(use.v), call.usage, `${where}: context call ${at} usage`);
    // A plain call that ran out of budget is not something a context call has
    // to reproduce: its ceilings are its creation's, and its scratch is
    // already there to be reused rather than grown.
    if (trial.outcome === MATCHED && got === MATCHED) {
      assert.deepEqual(offsets(ov.v), trial.ovector, `${where}: context call ${at} ovector`);
    }
  });
  if (one.context.edges !== undefined) {
    callEdges(held, one, one.context.edges, where, budget);
  }
};

// The per-call cost and stack edges. Memory is not a per-call limit on a
// context — the reservation is made once and a call takes no more — so the
// memory edge is creation's, and it was tested there.
const callEdges = (held, one, at, where, budget) => {
  const trial = one.trials[at];
  const subject = tir_bytes(unhex(trial.subject));
  const ov = tir_cell(tir_zero_vec_u32_512());
  const use = tir_cell(new Usage());
  const run = (cost, stack) =>
    ctx_match(held, subject, trial.start, trial.matchFlags, cost, stack, ov, use);
  const first = run(budget.memory, budget.stack);
  const answer = offsets(ov.v);
  const observed = usageOf(use.v);
  for (const name of ["cost", "stack"]) {
    const value = observed[name];
    const at = (spent) =>
      name === "cost" ? run(spent, budget.stack) : run(budget.memory, spent);
    assert.equal(at(value), first, `${where}: at the observed ${name} limit ${value}`);
    assert.deepEqual(offsets(ov.v), answer, `${where}: at the observed ${name} limit`);
    if (value === 0) {
      continue;
    }
    assert.equal(
      at(value - 1),
      REFUSED,
      `${where}: one below the observed ${name} limit ${value}`,
    );
  }
};

// A kept regression was found under limits of its own and goes on guarding
// under them; a generated case runs under the document's.
const sweepOne = (one, where, budget = BUDGET) => {
  const re = compiled(one, where);
  if (re === null) {
    return;
  }
  analysis(re, one, where);
  if (!one.pike) {
    ineligible(re, where, budget);
  }
  for (let at = 0; at < one.trials.length; at++) {
    oneTrial(re, one, at, `${where} trial ${at}`, budget);
  }
  context(re, one, where, budget);
};

test("the sweep shard", () => {
  for (const one of CORPUS.cases) {
    sweepOne(one, `${one.family}-${one.index}`);
  }
});

// The cases the sweep has actually found and a reducer has shrunk. They are
// kept rather than generated — a generated population is rebuilt from a seed
// and would not find them again once the seed moved on — and they are replayed
// through exactly the same battery, because what each one guards is an
// invariant rather than an answer.
test("the sweep regressions", () => {
  for (const one of list(CORPUS, "regressions", "sweep.json")) {
    assert.ok(one.budget, `${one.name}: a regression carries no budget of its own`);
    sweepOne(one, one.name, one.budget);
  }
});
