// Reading a conformance corpus, for the runners under test/.
//
// The envelope — the schema number and what a well-formed document looks like —
// lives in one place on the Python side (src/pcretruste/oracle/conformance.py)
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

export function load(name) {
  const path = fileURLToPath(new URL(`../../conformance/${name}`, import.meta.url));
  const document = JSON.parse(readFileSync(path, "utf8"));
  assert.equal(document.schema, SCHEMA, `${name} has an unexpected schema`);
  assert.ok(document.cases.length > 0, `${name} holds no cases`);
  return document;
}
