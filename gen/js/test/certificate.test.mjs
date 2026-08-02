// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated JavaScript. The same file runs against the Python interpreter and
// the generated Go, so agreeing with it is what "agreeing bit for bit" means.
//
// A certificate has no way in through the public API — the analysis accessors
// do not exist yet, and when they do they will take a subject length rather
// than a certificate — so this reaches into the generated module directly.

import { strict as assert } from "node:assert";
import test from "node:test";

import { load } from "../corpus.mjs";
import {
  BkCost,
  BkMem,
  BkStack,
  Cert,
  Region,
  Sum,
  Term,
  cert_bound,
  cert_check,
  tir_Seq,
} from "../engine.mjs";

const CORPUS = load("certificates.json");

const seq = (items) => new tir_Seq(items, items.length);

// The encoder writes TIR field names verbatim, so every key in the file is the
// field it names and the copy needs no mapping — only the two shapes the JSON
// cannot carry: the nested structs, and the sequence handle.
const buildSum = (one) => Object.assign(new Sum(), one);
const buildTerm = (one) => Object.assign(new Term(), one);

const buildRegion = (one) =>
  Object.assign(new Region(), one, {
    cost: buildSum(one.cost),
    stack: buildSum(one.stack),
    mem: buildSum(one.mem),
  });

const buildCert = (body) =>
  Object.assign(new Cert(), body, {
    regions: seq(body.regions.map(buildRegion)),
    terms: seq(body.terms.map(buildTerm)),
  });

const WHICH = [
  ["cost", BkCost],
  ["stack", BkStack],
  ["mem", BkMem],
];

test("the certificate corpus", () => {
  for (const one of CORPUS.cases) {
    const cert = buildCert(one.cert);
    assert.equal(cert_check(cert, one.codelen), one.check, `${one.name}: ${one.note}`);
    for (const at of one.bounds) {
      for (const [kind, which] of WHICH) {
        const got = cert_bound(cert, which, at.n);
        const want = at[kind];
        const where = `${one.name}: ${kind} at n=${at.n}`;
        // A null bound is ExceedsBudget, which is a refusal rather than a
        // number, so the value carries nothing and is not compared.
        assert.equal(got.ok, want !== null, where);
        if (want !== null) {
          assert.equal(got.value, want, where);
        }
      }
    }
  }
});
