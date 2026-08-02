// The README's JavaScript example, kept here so that it is run rather than
// admired. The only difference is that it returns the line instead of printing
// it, so the test has something to compare.

import { strict as assert } from "node:assert";
import test from "node:test";

import { compile, defaultLimits } from "../index.mjs";

function example() {
  const re = compile(String.raw`(?<user>\w+)@(?<host>[\w.]+)`);

  const subject = new TextEncoder().encode("write to alice@example.org, please");
  const ovector = re.match(subject, { limits: defaultLimits() });
  if (ovector === null) {
    return "no match";
  }

  const group = (n) =>
    new TextDecoder().decode(subject.subarray(ovector[2 * n], ovector[2 * n + 1]));
  return `${group(0)} is ${group(re.groupIndex("user"))} at ${group(re.groupIndex("host"))}`;
}

test("the README example", () => {
  assert.equal(example(), "alice@example.org is alice at example.org");
});
