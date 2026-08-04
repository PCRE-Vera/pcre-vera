// Reading a conformance corpus, for the runners under test/.
//
// The envelope — the schema number and what a well-formed document looks like —
// lives in one place on the Python side (src/pcrevera/oracle/conformance.py)
// for the reason its docstring gives: the runners check one schema against
// every corpus and would otherwise each have to be told which is which. This is
// that one place on the JavaScript side.
//
// It sits here rather than under test/ because `node --test` treats every
// module under a directory called test as a test file, and a helper that
// registers no tests would report as an empty one.

import { strict as assert } from "node:assert";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

export const SCHEMA = 1;

// Every byte string in a corpus is lowercase hex, because only the case's
// author knows how to read one as text.
export function unhex(text) {
  const bytes = new Uint8Array(text.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(text.slice(2 * i, 2 * i + 2), 16);
  }
  return bytes;
}

// What one element of each context array weighs, from BOUNDS.md section 3, and
// the sum a created context therefore holds: the arrays, plus the two result
// stores the wrapper materializes beside it — the engine ovector the run cores
// fill and the converted view a match answers through. Here rather than in a
// runner because both of them ask it, and a second copy of the table is a
// second thing to move when an array is added.
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

export function resident(ctx, re) {
  let total = 2 * (re.ncap + 1) * 4 * 2;
  for (const [name, esize] of WEIGHED) {
    total += ctx[name].a.length * esize;
  }
  return total;
}

// And the bytes a test spells as plain text, for the subjects and patterns a
// runner writes beside the corpus rather than in it.
export function ascii(text) {
  return Uint8Array.from(text, (c) => c.charCodeAt(0));
}

export function load(name) {
  return read(fileURLToPath(new URL(`../../conformance/${name}`, import.meta.url)), name);
}

// The same thing by path rather than by name, for the one corpus that has a
// bigger version of itself: a sweep campaign writes a result document of
// exactly the shard's shape, and replaying it here is what makes "the same
// manifest through all four implementations" true at campaign scale too.
export function read(path, name = path) {
  const document = JSON.parse(readFileSync(path, "utf8"));
  assert.equal(document.schema, SCHEMA, `${name} has an unexpected schema`);
  section(document, "cases", name);
  return document;
}

// One named array of a corpus, which may carry more than one: the certificate
// corpus holds the checker's cases and the analyzer's patterns separately,
// because the two halves of DESIGN.md section 5 are reached differently.
// Asking for a section by name is what keeps the "is this a corpus at all"
// rule here rather than at every place that reads a second one.
export function section(document, key, name) {
  const held = list(document, key, name);
  assert.ok(held.length > 0, `${name} holds no ${key}`);
  return held;
}

// And one that may legitimately be empty, but must be there: a repository that
// has not found an invariant failure yet has no sweep regressions to keep, and
// a runner that refused the empty list would refuse the shard of a clean
// checkout. A missing key is still an error, since that is what a typo looks
// like.
export function list(document, key, name) {
  const held = document[key];
  assert.ok(Array.isArray(held), `${name} has no ${key}`);
  return held;
}
