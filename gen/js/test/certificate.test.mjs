// The bound-certificate corpus of DESIGN.md section 8, run against the
// generated JavaScript. The same file runs against the Python interpreter and
// the generated Go, so agreeing with it is what "agreeing bit for bit" means.
//
// A certificate has no way in through the public API — the analysis accessors
// do not exist yet, and when they do they will take a subject length rather
// than a certificate — so this reaches into the generated module directly.

import { strict as assert } from "node:assert";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import test from "node:test";

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

const SCHEMA = 1;

const path = fileURLToPath(new URL("../../../conformance/certificates.json", import.meta.url));
const CORPUS = JSON.parse(readFileSync(path, "utf8"));

assert.equal(CORPUS.schema, SCHEMA, "the certificate corpus has an unexpected schema");
assert.ok(CORPUS.cases.length > 0, "the certificate corpus holds no cases");

const seq = (items) => new tir_Seq(items, items.length);

function buildSum(one) {
  const built = new Sum();
  built.first = one.first;
  built.count = one.count;
  return built;
}

function buildRegion(one) {
  const built = new Region();
  built.kind = one.kind;
  built.parent = one.parent;
  built.lo = one.lo;
  built.hi = one.hi;
  built.cost = buildSum(one.cost);
  built.stack = buildSum(one.stack);
  built.mem = buildSum(one.mem);
  return built;
}

function buildTerm(one) {
  const built = new Term();
  built.coef = one.coef;
  built.base = one.base;
  built.degree = one.degree;
  return built;
}

function buildCert(body) {
  const built = new Cert();
  built.config = body.config;
  built.complexity = body.complexity;
  built.regions = seq(body.regions.map(buildRegion));
  built.terms = seq(body.terms.map(buildTerm));
  return built;
}

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
