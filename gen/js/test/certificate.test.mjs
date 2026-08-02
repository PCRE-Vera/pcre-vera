// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated JavaScript. The same file runs against the Python interpreter and
// the generated Go, so agreeing with it is what "agreeing bit for bit" means.
//
// Every case names a pattern rather than a bytecode listing, so this compiles
// it here and hands the checker the program this backend would really run.
//
// A certificate has no way in through the public API — the analysis accessors
// do not exist yet, and when they do they will take a subject length rather
// than a certificate — so this reaches into the generated module directly.

import { strict as assert } from "node:assert";
import test from "node:test";

import { load, unhex } from "../corpus.mjs";
import {
  BkCost,
  BkMem,
  BkStack,
  CcLinear,
  Cert,
  CfgMemo,
  Out,
  Poly,
  Region,
  RkRepeat,
  cert_bound,
  cert_check,
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

const buildRegion = (one) =>
  Object.assign(new Region(), one, {
    kind: variant("Rk", one.kind, RkRepeat),
    work: buildPoly(one.work),
    outs: buildPoly(one.outs),
    stack: buildPoly(one.stack),
    trail: buildPoly(one.trail),
  });

const buildCert = (body) =>
  Object.assign(new Cert(), body, {
    config: variant("Cfg", body.config, CfgMemo),
    complexity: variant("Cc", body.complexity, CcLinear),
    cost: buildPoly(body.cost),
    stack: buildPoly(body.stack),
    mem: buildPoly(body.mem),
    regions: seq(body.regions.map(buildRegion)),
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

test("the certificate corpus", () => {
  for (const one of CORPUS.cases) {
    const where = `${one.name}: ${one.note}`;
    const cert = buildCert(one.cert);
    const re = buildProgram(one.pattern, where);
    const asked = variant("Cfg", one.config, CfgMemo);
    assert.equal(cert_check(re, asked, cert), one.check, where);
    for (const at of one.bounds) {
      for (const [kind, which] of WHICH) {
        const got = cert_bound(cert, which, at.n);
        const want = at[kind];
        const at_n = `${one.name}: ${kind} at n=${at.n}`;
        // A null bound is ExceedsBudget, which is a refusal rather than a
        // number, so the value carries nothing and is not compared.
        assert.equal(got.ok, want !== null, at_n);
        if (want !== null) {
          assert.equal(got.value, want, at_n);
        }
      }
    }
  }
});
