import Pcrevera.Tir.Decode
import Pcrevera.Tir.Toy

/-!
# The printer, against the writer that fixed the hash

`Tir/Print.lean` is a transcription of `tir/serialize.py`'s canonical writer,
and a transcription is only worth what it is checked against. So one program
is printed by both and the two texts compared here, byte for byte, at
elaboration time.

It is a small program on purpose — the artifact's own text is 2.8 megabytes
and belongs to gate 3, where it is decoded first — but it is not a trivial
one: it exercises the sorted top level, the sorted members of every nested
object, a nested array of statements, a `while` with its variant, a cast, a
comparison, an arithmetic operator and the two spellings of a literal.

The literal below came from `serialize.dumps` on the same program built out
of `tir/ir.py`, and it is meant to be regenerated that way rather than edited
by hand if the writer ever changes — which it cannot without moving the
artifact's hash, so in practice it never does.
-/

namespace Pcrevera.Tir

/-- What `serialize.dumps` writes for `sumProgram`, verbatim. -/
def sumCanonical : String :=
  "{\n  \"consts\": [],\n  \"enums\": [],\n  \"funcs\": [\n    {\n      \"body\": [\n        {\n          \"let\": {\n            \"init\": {\n              \"u32\": 0\n            },\n            \"name\": \"acc\",\n            \"type\": \"u32\"\n          }\n        },\n        {\n          \"let\": {\n            \"init\": {\n              \"u32\": 0\n            },\n            \"name\": \"i\",\n            \"type\": \"u32\"\n          }\n        },\n        {\n          \"while\": {\n            \"body\": [\n              {\n                \"assign\": {\n                  \"place\": {\n                    \"var\": \"i\"\n                  },\n                  \"value\": {\n                    \"bin\": {\n                      \"left\": {\n                        \"var\": \"i\"\n                      },\n                      \"op\": \"add\",\n                      \"right\": {\n                        \"u32\": 1\n                      }\n                    }\n                  }\n                }\n              },\n              {\n                \"assign\": {\n                  \"place\": {\n                    \"var\": \"acc\"\n                  },\n                  \"value\": {\n                    \"bin\": {\n                      \"left\": {\n                        \"var\": \"acc\"\n                      },\n                      \"op\": \"add\",\n                      \"right\": {\n                        \"var\": \"i\"\n                      }\n                    }\n                  }\n                }\n              }\n            ],\n            \"cond\": {\n              \"cmp\": {\n                \"left\": {\n                  \"var\": \"i\"\n                },\n                \"op\": \"lt\",\n                \"right\": {\n                  \"var\": \"n\"\n                }\n              }\n            },\n            \"variant\": {\n              \"bin\": {\n                \"left\": {\n                  \"cast\": {\n                    \"arg\": {\n                      \"var\": \"n\"\n                    },\n                    \"type\": \"counter\"\n                  }\n                },\n                \"op\": \"sub\",\n                \"right\": {\n                  \"cast\": {\n                    \"arg\": {\n                      \"var\": \"i\"\n                    },\n                    \"type\": \"counter\"\n                  }\n                }\n              }\n            }\n          }\n        },\n        {\n          \"return\": {\n            \"value\": {\n              \"var\": \"acc\"\n            }\n          }\n        }\n      ],\n      \"name\": \"sum\",\n      \"params\": [\n        {\n          \"mode\": \"in\",\n          \"name\": \"n\",\n          \"type\": \"u32\"\n        }\n      ],\n      \"ret\": \"u32\"\n    }\n  ],\n  \"structs\": [],\n  \"tir\": 1\n}\n"

#guard print sumProgram == sumCanonical

/-! ## The round trip

I-2's equation, checked here on the programs there are and proved on none:
`decode (print p) = ok p`. The decoder is the audited item and the printer is
exact, so what this catches is the two disagreeing about a constructor —
which is the only way a transcription of two documents into two functions
usually goes wrong.

Printing then decoding is checked on each toy program; decoding text a second
implementation wrote is checked on the one text there is of that kind, which
is `sumCanonical`. -/

/-- `Except` carries an error message, which is not what the round trip is
about; this asks only whether the decode landed on the program it started
from. -/
def decodedIs (r : D Program) (p : Program) : Bool :=
  match r with
  | .ok q => q == p
  | .error _ => false

def decodeFails (text : String) : Bool :=
  match decode text with
  | .ok _ => false
  | .error _ => true

#guard decodedIs (decode (print sumProgram)) sumProgram
#guard decodedIs (decode (print breakProgram)) breakProgram
#guard decodedIs (decode (print saturateProgram)) saturateProgram
#guard decodedIs (decode (print trapProgram)) trapProgram

-- And the other direction on the one text a second implementation wrote.
#guard decodedIs (decode sumCanonical) sumProgram

-- What the decoder refuses, so that "strict" is a fact and not a habit: a
-- top level that is not an object at all, one that is but has no schema
-- number, a schema number that is not this one, an unknown key, and a
-- fractional number where an integer belongs.
#guard decodeFails "[]"
#guard decodeFails "1"
#guard decodeFails "\"a\""
#guard decodeFails "null"
#guard decodeFails "true"
#guard decodeFails "{}"
#guard decodeFails "{\"tir\": 2, \"enums\": [], \"structs\": [], \"consts\": [], \"funcs\": []}"
#guard decodeFails "{\"tir\": 1, \"enums\": [], \"structs\": [], \"consts\": [], \"funcs\": [], \"extra\": 1}"
#guard decodeFails "{\"tir\": 1.5, \"enums\": [], \"structs\": [], \"consts\": [], \"funcs\": []}"
#guard decodedIs (decode "{\"tir\": 1, \"enums\": [], \"structs\": [], \"consts\": [], \"funcs\": []}") ⟨[], [], [], []⟩

end Pcrevera.Tir
