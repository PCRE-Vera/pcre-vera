// The conformance corpus of DESIGN.md section 8, run against the generated
// JavaScript. The same file runs against the Python interpreter and the
// generated Go, so agreeing with it is what "agreeing bit for bit" means.

import { strict as assert } from "node:assert";
import test from "node:test";

import { load } from "../corpus.mjs";
import { BSR, Kind, compile, defaultLimits } from "../index.mjs";
import { probe } from "../probe.mjs";

function unhex(text) {
  const bytes = new Uint8Array(text.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(text.slice(2 * i, 2 * i + 2), 16);
  }
  return bytes;
}

const latin1 = (bytes) => String.fromCharCode(...bytes);

const CORPUS = load("corpus.json");
const LOWERING = load("lowering.json");

function runCase(one) {
  const options = { flags: one.flags, newline: one.newline, bsr: one.bsr };
  let re;
  try {
    re = compile(unhex(one.pattern), options);
  } catch (failure) {
    if (one.expect.kind !== "compileError") {
      throw failure;
    }
    assert.equal(failure.code, one.expect.code, "compile error code");
    assert.equal(failure.offset, one.expect.offset, "compile error offset");
    return;
  }
  assert.notEqual(one.expect.kind, "compileError", "expected a compile error");

  if (one.expect.kind === "compiled") {
    assert.equal(re.groupCount, one.expect.captures, "capture count");
    const names = re.groupNames();
    assert.equal(names.size, Object.keys(one.expect.names).length, "named group count");
    for (const [encoded, number] of Object.entries(one.expect.names)) {
      assert.equal(re.groupIndex(latin1(unhex(encoded))), number, "group number");
    }
    return;
  }

  assert.ok(one.subject !== undefined, "a matching case needs a subject");
  const ovector = re.match(unhex(one.subject), {
    start: one.start,
    flags: one.matchFlags,
    limits: defaultLimits(),
  });
  if (one.expect.kind === "nomatch") {
    assert.equal(ovector, null, "expected no match");
    return;
  }
  assert.ok(ovector !== null, "expected a match");
  assert.deepEqual(Array.from(ovector), one.expect.ovector, "ovector");
}

test("the conformance corpus", () => {
  for (const one of CORPUS.cases) {
    try {
      runCase(one);
    } catch (failure) {
      failure.message = `${one.name}: ${failure.message}`;
      throw failure;
    }
  }
});

// The lowering probe is not part of the library. It exists so that the places
// where a printer can be silently wrong — a product that needs more than 53
// bits, a struct read that aliases, a growth schedule that rounds differently —
// are asked about directly rather than only through the engine.
test("the lowering probe", () => {
  for (const one of LOWERING.cases) {
    const answer = probe(one.kind, one.a, one.b);
    assert.equal(answer, one.expect, `${one.name}(${one.a}, ${one.b})`);
  }
});

test("the corpus really does reach the interesting outcomes", () => {
  // A corpus that quietly stopped exercising compile errors or captures would
  // still pass every assertion above, so the shape of it is checked too.
  const kinds = new Map();
  for (const one of CORPUS.cases) {
    kinds.set(one.expect.kind, (kinds.get(one.expect.kind) ?? 0) + 1);
  }
  for (const kind of ["match", "nomatch", "compileError", "compiled"]) {
    assert.ok(kinds.get(kind) > 0, `no ${kind} cases`);
  }
  // And one option that only the corpus reaches, so a wrong default shows up.
  assert.equal(Kind.SYNTAX, "syntax");
  assert.equal(BSR.ANYCRLF, 1);
});
