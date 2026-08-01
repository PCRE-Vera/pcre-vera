import { strict as assert } from "node:assert";
import test from "node:test";

import { artifactSha256, generated } from "../index.mjs";

test("the artifact hash and the generated flag agree", () => {
  assert.equal(generated(), artifactSha256 !== "");
  if (artifactSha256 !== "") {
    assert.match(artifactSha256, /^[0-9a-f]{64}$/);
  }
});
