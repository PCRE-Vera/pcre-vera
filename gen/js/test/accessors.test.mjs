// The accessors section of the certificate corpus, run against the public
// JavaScript wrapper. The same file runs against the Python driver and the Go
// wrapper, so the three languages answer identical statuses and identical
// numbers, refusals included.

import { strict as assert } from "node:assert";
import test from "node:test";

import { load, section, unhex } from "../corpus.mjs";
import {
  Complexity,
  Kind,
  MatchConfig,
  PcreError,
  compile,
} from "../index.mjs";

const CORPUS = load("certificates.json");

const STATUS_OK = 0;
const STATUS_BAD_INPUT = 3;
const STATUS_EXCEEDS_BUDGET = 4;

// An accessor call, folded back into the (status, value) pair the corpus
// pins: the wrapper's exceptions are its shape for the two refusals, and
// anything else it throws is a real failure.
const answered = (ask) => {
  try {
    return { status: STATUS_OK, value: ask() };
  } catch (failure) {
    assert.ok(failure instanceof PcreError);
    if (failure.kind === Kind.BAD_INPUT) {
      return { status: STATUS_BAD_INPUT, value: 0 };
    }
    assert.equal(failure.kind, Kind.EXCEEDS_BUDGET);
    return { status: STATUS_EXCEEDS_BUDGET, value: 0 };
  }
};

for (const entry of section(CORPUS, "accessors", "certificates.json")) {
  test(`accessors: ${entry.name}`, () => {
    const re = compile(unhex(entry.pattern));
    assert.deepEqual(
      answered(() => re.complexityClass()),
      entry.class,
      entry.note,
    );
    for (const query of entry.queries) {
      const asked = {
        config: query.config,
        n: query.n,
        cost: answered(() => re.worstCaseCost(query.n, query.config)),
        stack: answered(() => re.worstCaseStackEntries(query.n, query.config)),
        mem: answered(() => re.worstCaseMemory(query.n, query.config)),
        exercise: query.exercise,
      };
      assert.deepEqual(asked, query, entry.note);
      if (!query.exercise) {
        continue;
      }
      // The three bounds unchanged as the limits, and a run that may find or
      // not find but must not run out of them.
      const limits = {
        cost: query.cost.value,
        stack: query.stack.value,
        memory: query.mem.value,
      };
      const subject = new Uint8Array(query.n).fill(0x61);
      re.match(subject, { limits });
    }
  });
}

test("a length nothing represents is bad input", () => {
  // The corpus pins every length all three languages can spell; the ones only
  // JavaScript can — a fraction, a boolean, a negative, an unsafe number —
  // are pinned here, per the exact-integer rule of DESIGN.md section 2.4.
  const re = compile("abc");
  for (const length of [-1, 1.5, true, false, 2 ** 53, NaN, Infinity, "10", null]) {
    assert.throws(
      () => re.worstCaseCost(length, MatchConfig.DEFAULT),
      (failure) => failure.kind === Kind.BAD_INPUT,
      `length ${String(length)}`,
    );
  }
  for (const config of [-1, 0.5, true, 2 ** 32, "0"]) {
    assert.throws(
      () => re.worstCaseCost(10, config),
      (failure) => failure.kind === Kind.BAD_INPUT,
      `config ${String(config)}`,
    );
  }
});

test("the match configuration is part of the match surface", () => {
  const re = compile("abc");
  const subject = new Uint8Array([0x61, 0x62, 0x63]);
  assert.ok(re.match(subject, { config: MatchConfig.DEFAULT }));
  for (const config of [MatchConfig.MEMOIZED, 2, 0xffffffff, -1, 0.5, 2 ** 32]) {
    assert.throws(
      () => re.match(subject, { config }),
      (failure) => failure.kind === Kind.BAD_INPUT,
      `config ${String(config)}`,
    );
  }
});

test("the class constants are the pinned ordinals", () => {
  // The corpus speaks ordinals, so the named constants have to be them. A
  // star is linear now that it runs on the Pike VM; the counted repetition
  // keeps the backtracking path and its honest notProvenLinear.
  assert.equal(Complexity.NOT_PROVEN_LINEAR, 0);
  assert.equal(Complexity.LINEAR, 1);
  assert.equal(compile("abc").complexityClass(), Complexity.LINEAR);
  assert.equal(compile("a*").complexityClass(), Complexity.LINEAR);
  assert.equal(compile("a{0,2}b*").complexityClass(), Complexity.NOT_PROVEN_LINEAR);
});
