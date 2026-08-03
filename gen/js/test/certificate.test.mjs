// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated JavaScript. The same file runs against the Python interpreter and
// the generated Go, so agreeing with it is what "agreeing bit for bit" means.
//
// It has two halves, and so does this. The cases hand the checker a
// certificate; the analyses compile a pattern and read the one compilation
// produced. Either way the pattern is compiled here rather than described, so
// the engine is handed the program this backend would really run.
//
// A certificate has no way in through the public API — the analysis accessors
// take a subject length and answer a number, never a certificate — so this
// reaches into the generated module directly. The accessors themselves are
// held to the corpus's third section, in accessors.test.mjs, through the
// public wrapper.

import { strict as assert } from "node:assert";
import test from "node:test";

import { load, section, unhex } from "../corpus.mjs";
import {
  BkCost,
  BkMem,
  BkStack,
  CfgBacktrack,
  CrRegionWork,
  CrShape,
  CcLinear,
  Cert,
  CfgMemo,
  Out,
  Poly,
  Price,
  Region,
  RkRepeat,
  cert_bound,
  cert_build,
  cert_check,
  cert_shape,
  compile,
  tir_Seq,
  tir_bytes,
  tir_cell,
} from "../engine.mjs";

const CORPUS = load("certificates.json");

const seq = (items) => new tir_Seq(items, items.length);

// A TIR enum value is one of the variants it declares, and once printed it is a
// number like any other, so a decoder that used whatever the file held would
// hand the engine a value the IR has no meaning for. The Python side refuses a
// variant name its enum does not declare; this is the same refusal, spelt in
// the ordinals the file carries.
const variant = (what, ordinal, last) => {
  assert.ok(
    Number.isInteger(ordinal) && ordinal >= 0 && ordinal <= last,
    `${what} ordinal ${ordinal} names no variant`,
  );
  return ordinal;
};

// The encoder writes TIR field names verbatim, so every key in the file is the
// field it names and the copy needs no mapping — only the two shapes the JSON
// cannot carry: the nested structs, and the sequence handle.
const buildPoly = (one) => Object.assign(new Poly(), one);

const buildPrice = (one) =>
  Object.assign(new Price(), {
    work: buildPoly(one.work),
    outs: buildPoly(one.outs),
    stack: buildPoly(one.stack),
    trail: buildPoly(one.trail),
  });

// Only the cases about trees no compiler would emit carry one of these.
const buildRegion = (one) =>
  Object.assign(new Region(), one, { kind: variant("Rk", one.kind, RkRepeat) });

const buildCert = (body) =>
  Object.assign(new Cert(), body, {
    config: variant("Cfg", body.config, CfgMemo),
    complexity: variant("Cc", body.complexity, CcLinear),
    cost: buildPoly(body.cost),
    stack: buildPoly(body.stack),
    mem: buildPoly(body.mem),
    prices: seq(body.prices.map(buildPrice)),
  });

const buildProgram = (pattern, where) => {
  const out = tir_cell(new Out());
  compile(tir_bytes(unhex(pattern)), 0, 0, 0, out);
  assert.equal(out.v.err, 0, `${where}: the pattern does not compile`);
  return out.v.re;
};

const WHICH = [
  ["cost", BkCost],
  ["stack", BkStack],
  ["mem", BkMem],
];

// A null bound is ExceedsBudget, which is a refusal rather than a number, so
// the value carries nothing and is not compared.
const wantBounds = (cert, rows, where) => {
  for (const at of rows) {
    for (const [kind, which] of WHICH) {
      const got = cert_bound(cert, which, at.n);
      const want = at[kind];
      const at_n = `${where}: ${kind} at n=${at.n}`;
      assert.equal(got.ok, want !== null, at_n);
      if (want !== null) {
        assert.equal(got.value, want, at_n);
      }
    }
  }
};

test("the certificate corpus", () => {
  for (const one of CORPUS.cases) {
    const where = `${one.name}: ${one.note}`;
    const cert = buildCert(one.cert);
    const re = buildProgram(one.pattern, where);
    if (one.regions !== undefined) {
      re.regions = seq(one.regions.map(buildRegion));
    }
    const asked = variant("Cfg", one.config, CfgMemo);
    assert.equal(cert_check(re, asked, cert), one.check, where);
    // The checker without the certificate, which compilation runs on its own.
    // Which of the two halves answers each case is recorded rather than
    // derived here, so a check that moved from one half to the other fails
    // rather than passing either way.
    assert.equal(cert_shape(re), one.shape, `${where} (cert_shape)`);
    wantBounds(cert, one.bounds, one.name);
  }
});

// The other half: no certificate is handed in, because compiling the pattern
// is what produces one. What the corpus records is the analyzer's own verdict,
// then the class and the bounds of whatever compilation stored — and for a
// pattern with no representable bound, that the slot stayed empty.
test("the analyses of the certificate corpus", () => {
  for (const one of section(CORPUS, "analyses", "certificates.json")) {
    const where = `${one.name}: ${one.note}`;
    const re = buildProgram(one.pattern, where);
    const cand = tir_cell(new Cert());
    assert.equal(cert_build(re, cand), one.found, where);
    if (one.complexity === null) {
      assert.equal(re.hascert, false, `${where} (a pattern with no bound carries one)`);
      continue;
    }
    assert.equal(re.hascert, true, `${where} (compiling stored no certificate)`);
    // Both of them: the certificate compiling stored, and the one the analyzer
    // just handed back. A backend where those two differ has a compilation
    // that kept something other than what it computed, which nothing else here
    // would notice.
    for (const [what, cert] of [["stored", re.cert], ["built", cand.v]]) {
      assert.equal(cert.complexity, one.complexity, `${where} (${what})`);
      wantBounds(cert, one.bounds, `${one.name} (${what})`);
    }
  }
});

// A region kind outside the enum is not a TIR value at all, and in JavaScript
// it is a number like any other. What matters is that the checker says so
// rather than pricing the region at nothing, which would hide every
// instruction in its range behind a claim of zero.
test("a region kind outside the enum is refused", () => {
  const one = () => Object.assign(new Poly(), { base: 1, c0: 0, c1: 0, c2: 0, c3: 0, c4: 0 });
  const re = buildProgram("613f", "a?");
  const held = re.regions.a.slice(0, re.regions.n);
  assert.ok(held.length >= 2, "expected a tree with a region under the root");
  const prices = held.map(() =>
    Object.assign(new Price(), { work: one(), outs: one(), stack: one(), trail: one() }),
  );
  const cert = Object.assign(new Cert(), {
    config: CfgBacktrack,
    complexity: 0,
    cost: one(),
    stack: one(),
    mem: one(),
    prices: seq(prices),
  });
  // Claiming one of everything is far too little, so the answer is about the
  // numbers. What matters is that it is about the numbers at all.
  assert.equal(cert_check(re, CfgBacktrack, cert), CrRegionWork);
  held[held.length - 1].kind = 999;
  assert.equal(cert_check(re, CfgBacktrack, cert), CrShape);
  // A complexity class outside the enum is the same thing said of a field
  // rather than of a region: treating it as "not proven linear" would let a
  // caller name a class the engine has no claim for.
  held[held.length - 1].kind = RkRepeat;
  cert.complexity = 999;
  assert.equal(cert_check(re, CfgBacktrack, cert), CrShape);
  assert.equal(cert_bound(cert, 999, 4).ok, false);
});
