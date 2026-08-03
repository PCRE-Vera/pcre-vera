// The context section of the certificate corpus, run against the public
// JavaScript wrapper, plus the two claims the corpus cannot state. The
// physical one: the capacities a created context really holds, weighed at
// the IR sizes, sum to the memory bound. And the operational one, in the
// form it takes in this language: matching on a context constructs no
// backing store at all — no array, no typed array, no growth — because
// everything was reserved at creation. The strict zero-object-allocation
// claim is Go's; here the printed value semantics clone small records where
// Go copies stack values, and what the reservation is for is the stores.

import { strict as assert } from "node:assert";
import test from "node:test";

import { ascii, load, section, unhex } from "../corpus.mjs";
import { PcreError, compile } from "../index.mjs";
import {
  Ctx,
  compile as engineCompile,
  Out,
  ctx_create,
  re_mem,
  tir_bytes,
  tir_cell,
} from "../engine.mjs";

const CORPUS = load("certificates.json");
const ENTRIES = section(CORPUS, "contexts", "certificates.json");

const STATUS_MATCHED = 0;
const STATUS_NO_MATCH = 1;

const KIND_BY_STATUS = {
  2: "resourceExceeded",
  3: "badInput",
  4: "exceedsBudget",
};

const limitsOf = (row) => ({
  cost: row.cost,
  stack: row.stack,
  memory: row.memory,
});

const refused = (where, status, run) => {
  try {
    run();
  } catch (failure) {
    assert.ok(failure instanceof PcreError, where);
    assert.equal(failure.kind, KIND_BY_STATUS[status], where);
    return;
  }
  assert.fail(`${where}: expected a refusal with status ${status}`);
};

test("the context corpus", () => {
  for (const entry of ENTRIES) {
    const where = `${entry.name}: ${entry.note}`;
    const re = compile(unhex(entry.pattern));
    for (const row of entry.creations) {
      const make = () =>
        re.createContext(row.maxlen, {
          limits: limitsOf(row),
          config: row.config,
        });
      if (row.status !== 0) {
        refused(where, row.status, make);
        continue;
      }
      const held = make();
      // The reservation is pinned twice over: the number the corpus wrote
      // down, and this wrapper's own memory accessor at the declared
      // length.
      assert.equal(held.memory, row.memcap, where);
      assert.equal(held.memory, re.worstCaseMemory(row.maxlen), where);
      assert.equal(held.maxSubjectLen, row.maxlen, where);
    }
    if (entry.calls.length === 0) {
      continue;
    }
    const first = entry.creations[0];
    const held = re.createContext(entry.maxlen, { limits: limitsOf(first) });
    for (const [i, call] of entry.calls.entries()) {
      const at = `${entry.name}: call ${i}`;
      const options = { start: call.start };
      if (call.cost !== null) {
        options.costLimit = call.cost;
      }
      if (call.stack !== null) {
        options.stackLimit = call.stack;
      }
      if (call.status === STATUS_MATCHED) {
        const ovector = held.match(unhex(call.subject), options);
        assert.deepEqual(Array.from(ovector), call.ovector, at);
      } else if (call.status === STATUS_NO_MATCH) {
        assert.equal(held.match(unhex(call.subject), options), null, at);
      } else {
        refused(at, call.status, () => held.match(unhex(call.subject), options));
      }
    }
  }
});

// What one element of each array weighs, from BOUNDS.md section 3, restated
// so a context whose reservation drifted from the bound cannot agree with
// this sum.
const WEIGHED = [
  ["regs", 4],
  ["bt", 12],
  ["trail", 8],
  ["clist", 8],
  ["nlist", 8],
  ["stk", 8],
  ["seen", 1],
  ["rc", 4],
  ["free", 4],
  ["pool", 4],
  ["slack", 1],
];

test("a context is the memory bound made physical", () => {
  for (const [pattern, maxlen] of [
    ["abc", 64],
    ["(a)(b*)", 64],
    ["a*", 0],
    ["a{1,2}", 16],
    ["a{0,2}b*", 32],
    ["(ab)*c", 100],
  ]) {
    const out = tir_cell(new Out());
    engineCompile(tir_bytes(ascii(pattern)), 0, 0, 0, out);
    assert.equal(out.v.err, 0, pattern);
    const re = out.v.re;
    const held = tir_cell(new Ctx());
    const status = ctx_create(re, 0, maxlen, 2 ** 40, 100_000, 2 ** 31 - 1, held);
    assert.equal(status, 0, pattern);
    let resident = 0;
    for (const [name, esize] of WEIGHED) {
      resident += held.v[name].a.length * esize;
    }
    // Plus the two result stores the wrapper materializes beside the
    // context: the engine ovector the run cores fill, and the converted
    // view a match answers through.
    resident += 2 * (re.ncap + 1) * 4 * 2;
    assert.equal(resident, held.v.memcap, `${pattern} at ${maxlen}`);
    const bound = re_mem(re, 0, maxlen);
    assert.equal(bound.status, 0, pattern);
    assert.equal(bound.value, held.v.memcap, pattern);
  }
});

// Count every backing store the engine could construct while a patched
// window is open. The makers resolve the constructors from the global scope
// at call time, so a subclass planted there sees every store the generated
// code creates, growth included.
const counting = (run) => {
  let constructed = 0;
  const kinds = ["Array", "Uint8Array", "Uint32Array", "Int32Array", "Float64Array"];
  const held = new Map(kinds.map((kind) => [kind, globalThis[kind]]));
  for (const kind of kinds) {
    const Original = held.get(kind);
    // Delegating instanceof keeps values made outside the window passing
    // the wrapper's own type checks inside it.
    globalThis[kind] = class extends Original {
      constructor(...args) {
        super(...args);
        constructed += 1;
      }
      static [Symbol.hasInstance](value) {
        return value instanceof Original;
      }
    };
  }
  try {
    run();
  } finally {
    for (const kind of kinds) {
      globalThis[kind] = held.get(kind);
    }
  }
  return constructed;
};

test("matching on a context constructs no backing store", () => {
  // One pattern per execution path: the star rides the Pike VM, the counted
  // repetition stays on the backtracker.
  for (const pattern of ["(a)(b*)", "a{0,2}b*"]) {
    const re = compile(pattern);
    const held = re.createContext(64);
    const matching = ascii("aabb");
    const missing = ascii("zzz");
    const tooLong = new Uint8Array(65);
    // Warm and verified outside the window, then every path counted inside
    // it: a match, a miss, and each refusal.
    const first = held.match(matching);
    const stores = counting(() => {
      for (let i = 0; i < 10; i++) {
        held.match(matching);
        held.match(missing);
        try {
          held.match(tooLong);
        } catch {
          // BadInput, counted like every other path.
        }
        try {
          held.match(matching, { costLimit: 1 });
        } catch {
          // ResourceExceeded.
        }
      }
    });
    assert.equal(stores, 0, `${pattern}: ${stores} stores constructed`);
    // The answer rides one owned view for the life of the context.
    assert.equal(held.match(matching), first, pattern);
  }
});
