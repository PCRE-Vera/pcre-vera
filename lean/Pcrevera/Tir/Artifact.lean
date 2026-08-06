import Pcrevera.Tir.Decode

/-!
# The frozen artifact, decoded and printed back (I-3)

Where gate 2 quantifies over programs, this quantifies over nothing: it is one
closed statement about the bytes the backends were generated from.

    decode artifactText = ok P   and   print P = artifactText

The second half is what makes it a *canonicality* check rather than a parse.
A decoder that dropped a field, reordered members, or read a number loosely
would still decode; only printing what it decoded and comparing the text
catches that, and comparing the text is the same thing as comparing the hash
the whole project is pinned to.

The bytes are embedded at elaboration time, so this file cannot go stale
against `gen/engine.tir.json` — a regenerated artifact is a different string
here, and if it decodes and prints back to itself the check stays green while
`make verify` catches the drift elsewhere.

The hash below is not part of that check: nothing in this file reads it, and
elaboration would be just as happy without it. It is here so that the Lean
side names an artifact rather than merely holding one, and it is
`tests/test_lean_pin.py` that reads it back against the file on disk —
separately from `tests/test_freeze.py`, which reads the freeze record against
the same file. Two independent comparisons to one artifact, which is what
makes them worth having.
-/

namespace Pcrevera.Tir

/-- The exact bytes of `gen/engine.tir.json`, as of the `wave1-frozen` tag. -/
def artifactText : String := include_str "../../../gen/engine.tir.json"

/-- The sha256 the freeze record names, carried here so that the Lean side is
one more copy of it to read back rather than a place it could differ. -/
def artifactSha256 : String :=
  "d60df8a5600a4a0d4d1d1ea21e90883eab44d35a8f71e1d5450daf0a61b5dd1f"

/-- The artifact, as a program. -/
def artifact : D Program := decode artifactText

#guard match artifact with | .ok _ => true | .error _ => false

#guard match artifact with | .ok p => print p == artifactText | .error _ => false

end Pcrevera.Tir
