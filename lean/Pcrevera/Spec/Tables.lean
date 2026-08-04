import Pcrevera.Spec.Ast

/-!
# The byte vocabulary both layers share

ASCII case folding, the word set, and the three newline questions of the
pinned pcre2 build, exactly as `engine/vm.py` asks them. They live under
`Spec` because `Matches` needs them to say what an anchor or a caseless byte
means, and layer R uses the same definitions so the equivalence proof never
has to relate two spellings of "is this byte a newline".

Subjects are `ByteArray`; positions are `Nat`. Every read here guards its
index, mirroring the engine's own short-circuit tests.
-/


namespace Pcrevera

/-- ASCII case folding, all pcre2 does without PCRE2_UTF: A..Z gains 0x20. -/
def lowerByte (b : UInt8) : UInt8 :=
  if 0x41 ≤ b && b ≤ 0x5A then b + 0x20 else b

/-- The pinned build's \w set: ASCII letters, digits, underscore. -/
def isWordByte (b : UInt8) : Bool :=
  (0x61 ≤ b && b ≤ 0x7A) || (0x41 ≤ b && b ≤ 0x5A) ||
    (0x30 ≤ b && b ≤ 0x39) || b == 0x5F

/-- Byte at a position, `0` past the end. Callers guard the position the way
the engine's short-circuits do; the total read keeps definitions clean. -/
def byteAt (s : ByteArray) (pos : Nat) : UInt8 :=
  if h : pos < s.size then s[pos] else 0

/-- How many bytes of newline start at `pos`: 0 for none, 1 or 2 otherwise.
The engine's `newline_at`, question for question. -/
def newlineAt (s : ByteArray) (pos : Nat) (nl : NlType) : Nat :=
  if pos ≥ s.size then 0 else
  let c := byteAt s pos
  match nl with
  | .lf => if c == 0x0A then 1 else 0
  | .cr => if c == 0x0D then 1 else 0
  | .crlf =>
      if c == 0x0D && pos + 1 < s.size && byteAt s (pos + 1) == 0x0A then 2 else 0
  | .anycrlf =>
      if c == 0x0A then 1
      else if c == 0x0D then
        if pos + 1 < s.size && byteAt s (pos + 1) == 0x0A then 2 else 1
      else 0
  | .any =>
      if c == 0x0A then 1
      else if c == 0x0D then
        if pos + 1 < s.size && byteAt s (pos + 1) == 0x0A then 2 else 1
      else if c == 0x0B || c == 0x0C || c == 0x85 then 1
      else 0

/-- How many bytes of newline end at `pos`: the engine's `newline_before`. -/
def newlineBefore (s : ByteArray) (pos : Nat) (nl : NlType) : Nat :=
  if pos == 0 then 0 else
  match nl with
  | .lf => if byteAt s (pos - 1) == 0x0A then 1 else 0
  | .cr => if byteAt s (pos - 1) == 0x0D then 1 else 0
  | .crlf =>
      if pos ≥ 2 && byteAt s (pos - 2) == 0x0D && byteAt s (pos - 1) == 0x0A
      then 2 else 0
  | .anycrlf =>
      let c := byteAt s (pos - 1)
      if c == 0x0A then
        if pos ≥ 2 && byteAt s (pos - 2) == 0x0D then 2 else 1
      else if c == 0x0D then 1
      else 0
  | .any =>
      let c := byteAt s (pos - 1)
      if c == 0x0A then
        if pos ≥ 2 && byteAt s (pos - 2) == 0x0D then 2 else 1
      else if c == 0x0D then 1
      else if c == 0x0B || c == 0x0C || c == 0x85 then 1
      else 0

/-- What \R eats at `pos`: the engine's `bsr_at`. CR LF is one unit of 2,
lone CR or LF is 1, and the BSR_UNICODE extras are VT, FF, NEL. -/
def bsrAt (s : ByteArray) (pos : Nat) (bsr : BsrType) : Nat :=
  if pos ≥ s.size then 0 else
  let c := byteAt s pos
  if c == 0x0D then
    if pos + 1 < s.size && byteAt s (pos + 1) == 0x0A then 2 else 1
  else if c == 0x0A then 1
  else match bsr with
    | .anycrlf => 0
    | .unicode => if c == 0x0B || c == 0x0C || c == 0x85 then 1 else 0

/-- End of subject, or just before its final newline: the engine's
`at_line_end`, which is what plain `$` asks. -/
def atLineEnd (s : ByteArray) (pos : Nat) (nl : NlType) : Bool :=
  if pos ≥ s.size then true
  else
    let step := newlineAt s pos nl
    step != 0 && pos + step == s.size

/-- A word/non-word edge at `pos`: the engine's `word_edge`. -/
def wordEdge (s : ByteArray) (pos : Nat) : Bool :=
  let before := pos > 0 && isWordByte (byteAt s (pos - 1))
  let after := pos < s.size && isWordByte (byteAt s pos)
  before != after

/-- Whether the newline convention can see CR LF as one newline, which is the
half of the bumpalong condition that belongs to the convention. -/
def NlType.crlfish : NlType → Bool
  | .crlf | .anycrlf | .any => true
  | _ => false

end Pcrevera
