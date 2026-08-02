import { strict as assert } from "node:assert";
import test from "node:test";

import {
  BSR,
  Flags,
  Kind,
  MatchFlags,
  Newline,
  PcreError,
  artifactSha256,
  compile,
  defaultLimits,
  maxLength,
  maxMemoryLimit,
  maxStackLimit,
} from "../index.mjs";

const bytes = (text) => new TextEncoder().encode(text);

test("the artifact hash is a hash", () => {
  assert.match(artifactSha256, /^[0-9a-f]{64}$/);
});

test("compile and match", () => {
  const re = compile("(\\w+)@(\\w+)");
  assert.equal(re.groupCount, 2);
  const ovector = re.match(bytes("mail: alice@example"));
  assert.deepEqual(Array.from(ovector), [6, 19, 6, 11, 12, 19]);
});

test("no match is null rather than a throw", () => {
  assert.equal(compile("abc").match(bytes("xyz")), null);
});

test("a group that did not participate is -1", () => {
  const ovector = compile("(a)|(b)").match(bytes("b"));
  assert.deepEqual(Array.from(ovector), [0, 1, -1, -1, 0, 1]);
});

test("named groups", () => {
  const re = compile("(?<year>\\d{4})-(?<month>\\d{2})");
  assert.equal(re.groupIndex("month"), 2);
  assert.equal(re.groupIndex("day"), -1);
  const names = re.groupNames();
  assert.equal(names.size, 2);
  // The map is a copy, so writing to it cannot reach the pattern.
  names.set("year", 99);
  assert.equal(re.groupIndex("year"), 1);
});

test("a pattern may be raw bytes", () => {
  const ovector = compile(new Uint8Array([0x61, 0x2b])).match(bytes("caaab"));
  assert.deepEqual(Array.from(ovector), [1, 4]);
});

test("a string pattern above Latin-1 is refused until UTF mode", () => {
  // Not bad input: a pattern that wants UTF mode, which wave 3 brings. The
  // offset is the first code unit that asked for it.
  assert.throws(
    () => compile("ab日"),
    (error) =>
      error.kind === Kind.UNSUPPORTED_FEATURE && error.code === 1000 && error.offset === 2,
  );
  // Something that is neither bytes nor a string has nothing to support later.
  assert.throws(() => compile(42), (error) => error.kind === Kind.BAD_INPUT);
  // A code unit that still fits in a byte is read as that byte, so "café"
  // compiles and matches the four bytes it means rather than its UTF-8 form.
  assert.ok(compile("café").match(new Uint8Array([0x63, 0x61, 0x66, 0xe9])));
});

test("a syntax error carries the code and the offset", () => {
  assert.throws(
    () => compile("a[b"),
    (error) => {
      assert.ok(error instanceof PcreError);
      assert.equal(error.kind, Kind.SYNTAX);
      assert.equal(error.code, 106);
      assert.equal(error.offset, 3);
      return true;
    },
  );
});

test("an unsupported construct is not a pcre2 code", () => {
  assert.throws(
    () => compile("(?=a)"),
    (error) => error.kind === Kind.UNSUPPORTED_FEATURE && error.code >= 1000,
  );
});

test("options reach the engine", () => {
  assert.equal(compile("ABC").match(bytes("abc")), null);
  assert.ok(compile("ABC", { flags: Flags.CASELESS }).match(bytes("abc")));
  assert.equal(compile("^b", { flags: Flags.MULTILINE }).match(bytes("a\nb"))[0], 2);
  assert.ok(compile("\\R", { bsr: BSR.ANYCRLF }).match(bytes("\r")));
  assert.equal(compile("a$", { newline: Newline.CRLF }).match(bytes("a\r\nb")), null);
});

test("match options reach the engine", () => {
  const re = compile("^a");
  assert.equal(re.match(bytes("a"), { flags: MatchFlags.NOTBOL }), null);
  assert.equal(compile("b*").match(bytes("a"), { flags: MatchFlags.NOTEMPTY }), null);
});

test("a start offset outside the subject is bad input", () => {
  const re = compile("a");
  assert.throws(() => re.match(bytes("aaa"), { start: 4 }), (e) => e.kind === Kind.BAD_INPUT);
  assert.throws(() => re.match(bytes("aaa"), { start: 1.5 }), (e) => e.kind === Kind.BAD_INPUT);
  assert.throws(() => re.match(bytes("aaa"), { start: -1 }), (e) => e.kind === Kind.BAD_INPUT);
  assert.equal(re.match(bytes("aaa"), { start: 3 }), null);
});

test("a limit past what any target could honor is bad input", () => {
  const re = compile("a");
  const limits = defaultLimits();
  limits.memory = maxMemoryLimit + 1;
  assert.throws(() => re.match(bytes("a"), { limits }), (e) => e.kind === Kind.BAD_INPUT);
  assert.throws(
    () => re.match(bytes("a"), { limits: { cost: 1.5, stack: 1, memory: 1 } }),
    (e) => e.kind === Kind.BAD_INPUT,
  );
  assert.throws(
    () => re.match(bytes("a"), { limits: { cost: NaN, stack: 1, memory: 1 } }),
    (e) => e.kind === Kind.BAD_INPUT,
  );
});

test("a match over budget is resource exceeded", () => {
  const re = compile("(a*)*b");
  const limits = { cost: 32, stack: maxStackLimit, memory: maxMemoryLimit };
  assert.throws(
    () => re.match(bytes("a".repeat(40)), { limits }),
    (error) => error.kind === Kind.RESOURCE_EXCEEDED,
  );
});

test("a subject has to be bytes", () => {
  assert.throws(() => compile("a").match("a"), (error) => error.kind === Kind.BAD_INPUT);
});

test("an options argument that is not an object is bad input", () => {
  const re = compile("a");
  assert.throws(() => compile("a", null), (e) => e.kind === Kind.BAD_INPUT);
  assert.throws(() => compile("a", 7), (e) => e.kind === Kind.BAD_INPUT);
  assert.throws(() => re.match(bytes("a"), null), (e) => e.kind === Kind.BAD_INPUT);
  assert.throws(
    () => re.match(bytes("a"), { limits: null }),
    (e) => e.kind === Kind.BAD_INPUT,
  );
  // Omitting them entirely is what the defaults are for.
  assert.ok(compile("a", undefined).match(bytes("a"), undefined));
});

test("a subject no i32 offset could describe is bad input", () => {
  // Allocating 2 GiB to prove this would be unkind, so the length is faked;
  // what the check has to reject is a length, not an allocation.
  class Oversize extends Uint8Array {
    get length() {
      return maxLength + 1;
    }
  }
  assert.throws(
    () => compile("a").match(new Oversize(0)),
    (error) => error.kind === Kind.BAD_INPUT,
  );
});
