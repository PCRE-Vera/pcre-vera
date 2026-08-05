import Pcrevera.Proofs.RepBounds

/-!
# Where a counted repetition's opcodes sit (BOUNDS.md section 4.4)

`code_ok_of_cert` reads forwardness off an accepted certificate, but only for
a program whose repeat regions are all optional items. `CodeOk` refuses the
four repetition opcodes by construction, `Op.loose` being the only opcode
clause it has, so it says nothing about a program that really counts. What
follows is the same walk over the region tree with the counted arm of
`shape_repeat` opened instead of `shapeRepeat_opt`, and what comes out of it
is `RepFwd`, the forwardness `repCostAt` asks for, together with where each
repetition opcode sits.

The layout is entirely `shape_repeat`'s doing. A counted region is `RepZero`,
`RepLoop`, `RepEnter`, a body, and `RepNext`, and the repetition record the
header names has to agree with all three of the offsets the code generator
fixed: the head is the `RepLoop`, the body entry is the `RepEnter`, and the
exit is the end of the region. So the four opcodes sit at the four positions
the record names, and the body cannot hold another one of them — it is walked
as an ordinary span, which admits loose opcodes and child regions and refuses
everything else by name.

That last point is what the pricing needs downstream. A repetition index is
read off the record rather than off the region, so two opcodes naming the same
index are inside one region's range, and a walk that has left that range never
reads the counter again.

Only the shape half of a certificate is used here. The prices say nothing
about the layout, and `rep_code_ok_of_cert` takes a whole accepted certificate
only because that is what its callers have in hand.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## Where a repetition opcode may sit -/

/-- The four positions a repetition's own record names: the `RepZero` one
before its head, the head, the body entry, and the `RepNext` one before its
exit. The distances between the offsets are pinned too, because those are
what turn a position into a range. -/
def RepAt (re : Re) (q r : Nat) : Prop :=
  r < re.reps.size ∧
    (q = (re.reps[r]!).head - 1 ∨ q = (re.reps[r]!).head ∨
      q = (re.reps[r]!).body ∨ q = (re.reps[r]!).after - 1) ∧
    (re.reps[r]!).body = (re.reps[r]!).head + 1 ∧
    (re.reps[r]!).head + 3 ≤ (re.reps[r]!).after

/-- And so such a position is inside the repetition's own range. This is the
fact the pricing really wants: past the exit there is no opcode left that
reads the counter. -/
theorem RepAt.inside {re : Re} {q r : Nat} (h : RepAt re q r) :
    (re.reps[r]!).head - 1 ≤ q ∧ q < (re.reps[r]!).after := by
  obtain ⟨-, hq, hbody, hafter⟩ := h
  rcases hq with h | h | h | h <;> omega

/-! ## What the pricing needs of one instruction -/

/-- A program that ends in an `Accept` never falls off its own end anywhere
else, because the only instruction with nothing after it is that `Accept`. -/
theorem onward_of_last {re : Re} {q : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (hq : q < re.code.size)
    (hop : (re.code[q]!).op ≠ .accept) : q + 1 < re.code.size := by
  rcases Nat.lt_or_ge (q + 1) re.code.size with h | h
  · exact h
  · have hqe : q = re.code.size - 1 := by omega
    rw [hqe] at hop
    exact absurd hlast hop

/-- `CodeOk` with the repetition opcodes admitted rather than refused.

The first four clauses are the forward pricing's, unchanged: the arms of a
split and the target of a jump are ahead and inside the program, and control
falls through into the program rather than off it. The rest is what a counted
repetition adds — where the opcode sits, and, for the two that name a target,
what the record they read it from says. -/
structure RepCodeOk (re : Re) (q : Nat) : Prop where
  fwd : RepFwd re q
  split : (re.code[q]!).op = .split →
    (re.code[q]!).arg < re.code.size ∧ (re.code[q]!).alt < re.code.size
  jump : (re.code[q]!).op = .jump → (re.code[q]!).arg < re.code.size
  onward : (re.code[q]!).op ≠ .accept → q + 1 < re.code.size
  ranged : ((re.code[q]!).op = .repZero ∨ (re.code[q]!).op = .repLoop ∨
      (re.code[q]!).op = .repEnter ∨ (re.code[q]!).op = .repNext) →
    RepAt re q (re.code[q]!).arg
  loop : (re.code[q]!).op = .repLoop →
    q = (re.reps[(re.code[q]!).arg]!).head ∧
      (re.reps[(re.code[q]!).arg]!).body = q + 1
  head : (re.code[q]!).op = .repNext →
    (re.code[(re.reps[(re.code[q]!).arg]!).head]!).op = .repLoop ∧
      (re.code[(re.reps[(re.code[q]!).arg]!).head]!).arg = (re.code[q]!).arg

/-- An instruction a region may hold loose satisfies every clause but the
fall-through outright, and that one is the program's `Accept`. -/
theorem RepCodeOk.ofLoose {re : Re} {q : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (hq : q < re.code.size)
    (h : (re.code[q]!).op.loose = true) : RepCodeOk re q := by
  refine ⟨⟨fun hop => ?_, fun hop => ?_, fun hop => ?_⟩, fun hop => ?_,
    fun hop => ?_, fun hop => onward_of_last hlast hq hop, fun hop => ?_,
    fun hop => ?_, fun hop => ?_⟩
  · rw [hop] at h; exact absurd h (by decide)
  · rw [hop] at h; exact absurd h (by decide)
  · rcases hop with hop | hop <;> (rw [hop] at h; exact absurd h (by decide))
  · rw [hop] at h; exact absurd h (by decide)
  · rw [hop] at h; exact absurd h (by decide)
  · rcases hop with hop | hop | hop | hop <;>
      (rw [hop] at h; exact absurd h (by decide))
  · rw [hop] at h; exact absurd h (by decide)
  · rw [hop] at h; exact absurd h (by decide)

/-- A split whose two arms are ahead of it and inside the program. -/
theorem repCodeOk_split {re : Re} {q a b : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (hq : q < re.code.size)
    (hop : (re.code[q]!).op = .split)
    (harg : (re.code[q]!).arg = a) (halt : (re.code[q]!).alt = b)
    (ha : q < a ∧ a < re.code.size) (hb : q < b ∧ b < re.code.size) :
    RepCodeOk re q := by
  refine ⟨⟨fun _ => ?_, fun hj => ?_, fun hr => ?_⟩, fun _ => ?_, fun hj => ?_,
    fun _ => onward_of_last hlast hq (by rw [hop]; decide), fun hr => ?_,
    fun hl => ?_, fun hn => ?_⟩
  · rw [harg, halt]; exact ⟨ha.1, hb.1⟩
  · rw [hop] at hj; exact absurd hj (by decide)
  · rcases hr with h | h <;> (rw [hop] at h; exact absurd h (by decide))
  · rw [harg, halt]; exact ⟨ha.2, hb.2⟩
  · rw [hop] at hj; exact absurd hj (by decide)
  · rcases hr with h | h | h | h <;> (rw [hop] at h; exact absurd h (by decide))
  · rw [hop] at hl; exact absurd hl (by decide)
  · rw [hop] at hn; exact absurd hn (by decide)

/-- A jump whose target is ahead of it and inside the program. -/
theorem repCodeOk_jump {re : Re} {q a : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (hq : q < re.code.size)
    (hop : (re.code[q]!).op = .jump) (harg : (re.code[q]!).arg = a)
    (ha : q < a ∧ a < re.code.size) : RepCodeOk re q := by
  refine ⟨⟨fun hs => ?_, fun _ => ?_, fun hr => ?_⟩, fun hs => ?_, fun _ => ?_,
    fun _ => onward_of_last hlast hq (by rw [hop]; decide), fun hr => ?_,
    fun hl => ?_, fun hn => ?_⟩
  · rw [hop] at hs; exact absurd hs (by decide)
  · rw [harg]; exact ha.1
  · rcases hr with h | h <;> (rw [hop] at h; exact absurd h (by decide))
  · rw [hop] at hs; exact absurd hs (by decide)
  · rw [harg]; exact ha.2
  · rcases hr with h | h | h | h <;> (rw [hop] at h; exact absurd h (by decide))
  · rw [hop] at hl; exact absurd hl (by decide)
  · rw [hop] at hn; exact absurd hn (by decide)

/-- A repetition opcode. None of the four forks or jumps, and the two that do
name a target read it through the record rather than off the instruction — so
where the opcode sits is the whole of what `RepFwd` needs from it. -/
theorem RepCodeOk.ofRep {re : Re} {q : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (hq : q < re.code.size)
    (hop : (re.code[q]!).op = .repZero ∨ (re.code[q]!).op = .repLoop ∨
      (re.code[q]!).op = .repEnter ∨ (re.code[q]!).op = .repNext)
    (hrep : RepAt re q (re.code[q]!).arg)
    (hloop : (re.code[q]!).op = .repLoop → q = (re.reps[(re.code[q]!).arg]!).head)
    (hhead : (re.code[q]!).op = .repNext →
      (re.code[(re.reps[(re.code[q]!).arg]!).head]!).op = .repLoop ∧
        (re.code[(re.reps[(re.code[q]!).arg]!).head]!).arg = (re.code[q]!).arg) :
    RepCodeOk re q := by
  have hnacc : (re.code[q]!).op ≠ .accept := by
    rcases hop with h | h | h | h <;> (rw [h]; decide)
  refine ⟨⟨fun hs => ?_, fun hj => ?_, fun _ => hrep.inside.2⟩, fun hs => ?_,
    fun hj => ?_, fun _ => onward_of_last hlast hq hnacc, fun _ => hrep,
    fun hl => ⟨hloop hl, by have hb := hrep.2.2.1; have hh := hloop hl; omega⟩,
    hhead⟩
  · rcases hop with h | h | h | h <;> (rw [h] at hs; exact absurd hs (by decide))
  · rcases hop with h | h | h | h <;> (rw [h] at hj; exact absurd hj (by decide))
  · rcases hop with h | h | h | h <;> (rw [h] at hs; exact absurd hs (by decide))
  · rcases hop with h | h | h | h <;> (rw [h] at hj; exact absurd hj (by decide))

/-- The five-part header of a counted repetition, read back one position at a
time. Everything here is `shape_repeat`'s: the four opcodes, the repetition
index each of them names, and the three offsets the record has to agree with.
A `RepNext` finds a `RepLoop` at the head it names for the same reason the
`RepLoop` finds itself there — the record's head is the second instruction of
the region, and that is the one holding the `RepLoop`. -/
theorem repCodeOk_header {re : Re} {lo hi r q : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hhi : hi < re.code.size) (h4 : lo + 4 ≤ hi) (hsize : r < re.reps.size)
    (hzero : (re.code[lo]!).op = .repZero) (hzarg : (re.code[lo]!).arg = r)
    (hloop : (re.code[lo + 1]!).op = .repLoop)
    (hlarg : (re.code[lo + 1]!).arg = r)
    (henter : (re.code[lo + 2]!).op = .repEnter)
    (hearg : (re.code[lo + 2]!).arg = r)
    (htail : (re.code[hi - 1]!).op = .repNext)
    (htarg : (re.code[hi - 1]!).arg = r)
    (hhead : (re.reps[r]!).head = lo + 1) (hbody : (re.reps[r]!).body = lo + 2)
    (hafter : (re.reps[r]!).after = hi)
    (hq : q = lo ∨ q = lo + 1 ∨ q = lo + 2 ∨ q = hi - 1) : RepCodeOk re q := by
  have hat : ∀ p : Nat, (re.code[p]!).arg = r →
      (p = lo ∨ p = lo + 1 ∨ p = lo + 2 ∨ p = hi - 1) →
      RepAt re p (re.code[p]!).arg := by
    intro p hp hpq
    rw [hp]
    exact ⟨hsize, by rcases hpq with h | h | h | h <;> omega, by omega, by omega⟩
  rcases hq with rfl | rfl | rfl | rfl
  · exact RepCodeOk.ofRep hlast (by omega) (Or.inl hzero) (hat _ hzarg (Or.inl rfl))
      (fun hl => by rw [hzero] at hl; exact absurd hl (by decide))
      (fun hn => by rw [hzero] at hn; exact absurd hn (by decide))
  · exact RepCodeOk.ofRep hlast (by omega) (Or.inr (Or.inl hloop))
      (hat _ hlarg (Or.inr (Or.inl rfl))) (fun _ => by rw [hlarg, hhead])
      (fun hn => by rw [hloop] at hn; exact absurd hn (by decide))
  · exact RepCodeOk.ofRep hlast (by omega) (Or.inr (Or.inr (Or.inl henter)))
      (hat _ hearg (Or.inr (Or.inr (Or.inl rfl))))
      (fun hl => by rw [henter] at hl; exact absurd hl (by decide))
      (fun hn => by rw [henter] at hn; exact absurd hn (by decide))
  · exact RepCodeOk.ofRep hlast (by omega) (Or.inr (Or.inr (Or.inr htail)))
      (hat _ htarg (Or.inr (Or.inr (Or.inr rfl))))
      (fun hl => by rw [htail] at hl; exact absurd hl (by decide))
      (fun _ => by rw [htarg, hhead]; exact ⟨hloop, hlarg⟩)

/-! ## The counted arm of `shape_repeat` -/

/-- A repeat region begins with a split or with a `RepZero`, because
`shape_repeat` refuses everything else at that point. -/
theorem shapeRepeat_head {code : Array Inst} {reps : Array RepInfo}
    {regions : Array Region} {sibs : Array Nat} {at_ first : Nat}
    (h : shapeRepeat code reps regions sibs at_ first = .crOk) :
    (code[(regions[at_]!).lo]!).op = .split ∨
      (code[(regions[at_]!).lo]!).op = .repZero := by
  rw [shapeRepeat] at h
  dsimp only at h
  by_cases h1 : (regions[at_]!).hi ≤ (regions[at_]!).lo
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  rw [if_neg h1] at h
  by_cases hsp : (code[(regions[at_]!).lo]!).op = .split
  · exact Or.inl hsp
  rw [if_neg hsp] at h
  by_cases hz : (code[(regions[at_]!).lo]!).op ≠ .repZero
  · rw [if_pos hz] at h
    exact absurd h (by decide)
  · simp only [ne_eq, Decidable.not_not] at hz
    exact Or.inr hz

/-- BOUNDS.md section 4.4's shape, read whole. The header is the four
repetition opcodes at the two ends of the region, all naming one repetition;
the record that repetition index reaches has its head, its body entry and its
exit where the header put them; and what is between the `RepEnter` and the
`RepNext` is an ordinary span.

Between those and the region's own range there is nothing left for a repeat
region to choose, which is why it carries no witness field. -/
theorem shapeRepeat_counted {code : Array Inst} {reps : Array RepInfo}
    {regions : Array Region} {sibs : Array Nat} {at_ first : Nat}
    (hhead : (code[(regions[at_]!).lo]!).op = .repZero)
    (h : shapeRepeat code reps regions sibs at_ first = .crOk) :
    (regions[at_]!).lo + 4 ≤ (regions[at_]!).hi ∧
      (code[(regions[at_]!).lo]!).arg < reps.size ∧
      (code[(regions[at_]!).lo + 1]!).op = .repLoop ∧
      (code[(regions[at_]!).lo + 1]!).arg = (code[(regions[at_]!).lo]!).arg ∧
      (code[(regions[at_]!).lo + 2]!).op = .repEnter ∧
      (code[(regions[at_]!).lo + 2]!).arg = (code[(regions[at_]!).lo]!).arg ∧
      (code[(regions[at_]!).hi - 1]!).op = .repNext ∧
      (code[(regions[at_]!).hi - 1]!).arg = (code[(regions[at_]!).lo]!).arg ∧
      (reps[(code[(regions[at_]!).lo]!).arg]!).head = (regions[at_]!).lo + 1 ∧
      (reps[(code[(regions[at_]!).lo]!).arg]!).body = (regions[at_]!).lo + 2 ∧
      (reps[(code[(regions[at_]!).lo]!).arg]!).after = (regions[at_]!).hi ∧
      shapeSpan code regions sibs ((regions[at_]!).lo + 3)
        ((regions[at_]!).hi - 1) first = .crOk := by
  rw [shapeRepeat] at h
  dsimp only at h
  by_cases h1 : (regions[at_]!).hi ≤ (regions[at_]!).lo
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  rw [if_neg h1, if_neg (by simp [hhead]), if_neg (by simp [hhead])] at h
  by_cases h4 : (regions[at_]!).hi - (regions[at_]!).lo < 4
  · rw [if_pos h4] at h
    exact absurd h (by decide)
  rw [if_neg h4] at h
  by_cases hwhich : (code[(regions[at_]!).lo]!).arg ≥ reps.size
  · rw [if_pos hwhich] at h
    exact absurd h (by decide)
  rw [if_neg hwhich] at h
  by_cases hloop : (code[(regions[at_]!).lo + 1]!).op ≠ .repLoop ∨
      (code[(regions[at_]!).lo + 1]!).arg ≠ (code[(regions[at_]!).lo]!).arg
  · rw [if_pos hloop] at h
    exact absurd h (by decide)
  rw [if_neg hloop] at h
  by_cases henter : (code[(regions[at_]!).lo + 2]!).op ≠ .repEnter ∨
      (code[(regions[at_]!).lo + 2]!).arg ≠ (code[(regions[at_]!).lo]!).arg
  · rw [if_pos henter] at h
    exact absurd h (by decide)
  rw [if_neg henter] at h
  by_cases htail : (code[(regions[at_]!).hi - 1]!).op ≠ .repNext ∨
      (code[(regions[at_]!).hi - 1]!).arg ≠ (code[(regions[at_]!).lo]!).arg
  · rw [if_pos htail] at h
    exact absurd h (by decide)
  rw [if_neg htail] at h
  by_cases hoff :
      (reps[(code[(regions[at_]!).lo]!).arg]!).head ≠ (regions[at_]!).lo + 1 ∨
      (reps[(code[(regions[at_]!).lo]!).arg]!).body ≠ (regions[at_]!).lo + 2 ∨
      (reps[(code[(regions[at_]!).lo]!).arg]!).after ≠ (regions[at_]!).hi
  · rw [if_pos hoff] at h
    exact absurd h (by decide)
  rw [if_neg hoff] at h
  simp only [not_or, ne_eq, Decidable.not_not] at hloop henter htail hoff
  exact ⟨by omega, by omega, hloop.1, hloop.2, henter.1, henter.2, htail.1,
    htail.2, hoff.1, hoff.2.1, hoff.2.2, h⟩

/-! ## The two walks that cover a region's range -/

/-- The section 4.1 walk read as coverage, off `shape_span` rather than off
the price walk. Whatever holds of every loose opcode and of every child's
range holds of the whole range, because those two are all a straight-line
region contains — and the walk refuses a child reaching past the range, which
is what lets a repeat region's body be covered without knowing where the
children of the region end. -/
theorem shapeSpanGo_covers {code : Array Inst} {regions : Array Region}
    {sibs : Array Nat} {hi : Nat} {Q : Nat → Prop}
    (hloose : ∀ q : Nat, (code[q]!).op.loose = true → Q q)
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      ∀ q, (regions[c]!).lo ≤ q → q < (regions[c]!).hi → Q q) :
    ∀ (k pc cursor : Nat), P cursor → hi - pc ≤ k →
      shapeSpanGo code regions sibs hi pc cursor = .crOk →
      ∀ q, pc ≤ q → q < hi → Q q := by
  intro k
  induction k with
  | zero =>
      intro pc cursor _ hk _ q h1 h2
      omega
  | succ k ih =>
      intro pc cursor hP hk h q h1 h2
      rw [shapeSpanGo, dif_pos (show pc < hi by omega)] at h
      by_cases hback : (cursor != none32 && (regions[cursor]!).lo < pc) = true
      · rw [if_pos hback] at h
        exact absurd h (by decide)
      rw [if_neg hback] at h
      by_cases hhit : (cursor != none32 && (regions[cursor]!).lo == pc) = true
      · rw [if_pos hhit] at h
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hhit
        by_cases hkhi : (regions[cursor]!).hi ≤ pc
        · rw [dif_pos hkhi] at h
          exact absurd h (by decide)
        rw [dif_neg hkhi] at h
        by_cases hover : (regions[cursor]!).hi > hi
        · rw [if_pos hover] at h
          exact absurd h (by decide)
        rw [if_neg hover] at h
        by_cases hin : q < (regions[cursor]!).hi
        · exact hkid cursor hP hhit.1 q (by rw [hhit.2]; omega) hin
        · exact ih (regions[cursor]!).hi (sibs[cursor]!) (hsib cursor hP hhit.1)
            (by omega) h q (by omega) h2
      rw [if_neg hhit] at h
      split at h
      all_goals rename_i hop
      all_goals
        first
          | exact absurd h (by decide)
          | (rcases Nat.eq_or_lt_of_le h1 with rfl | h3
             · exact hloose _ (by rw [hop]; rfl)
             · exact ih (pc + 1) _ hP (by omega) h q (by omega) h2)

/-- The same for an alternation. Its range is a split, a branch, a jump and
the rest of the chain, and `shape_alt` has pinned each split and each jump to
a later instruction; the end of the alternation is inside the program, which
is what all of them target. -/
theorem shapeAltGo_rep_ok {re : Re} {sibs : Array Nat} {hi : Nat}
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (hhi : hi < re.code.size)
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hle : ∀ c : Nat, P c → c ≠ none32 →
      (re.regions[c]!).lo ≤ (re.regions[c]!).hi)
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      ∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi → RepCodeOk re q) :
    ∀ (fuel p c k : Nat), P c →
      shapeAltGo re.code re.regions sibs hi fuel p c k = .crOk → c ≠ none32 →
      ∀ q, p ≤ q → q < hi → RepCodeOk re q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p c k _ h hne q _ _
      rw [shapeAltGo, if_pos hne] at h
      exact absurd h (by decide)
  | succ fuel ih =>
      intro p c k hP h hne q h1 h2
      rcases shapeAltGo_step hne h with
        ⟨hnxt, hph, hforkop, harg, hclo, hstop, hleaveop, hleavearg, halt, hrec⟩ |
        ⟨hnxt, hclo, hchi, hrec⟩
      · have hlh := hle c hP hne
        by_cases hq : q = p
        · subst hq
          exact repCodeOk_split hlast (by omega) hforkop harg halt
            ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        by_cases hq2 : q < (re.regions[c]!).hi
        · exact hkid c hP hne q (by omega) hq2
        by_cases hq3 : q = (re.regions[c]!).hi
        · subst hq3
          exact repCodeOk_jump hlast (by omega) hleaveop hleavearg
            ⟨by omega, by omega⟩
        · exact ih ((re.regions[c]!).hi + 1) (sibs[c]!) (k + 1) (hsib c hP hne)
            hrec hnxt q (by omega) h2
      · exact hkid c hP hne q (by omega) (by omega)

/-! ## The tree induction -/

/-- The walk downwards over the region tree, with the counted arm opened. A
straight-line region's range is covered by its own span walk and by its
children, an alternation's by `shape_alt` and by its branches, and a repeat
region's either by the split at its head and the body after it, or by the
five-part header and the span between the `RepEnter` and the `RepNext`. Every
child has a larger index than its parent, so walking the index downwards
covers every region's range, and the root's range is the program. -/
theorem region_rep_code_ok {re : Re}
    (hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i)
    (hrange : ∀ i, i < re.regions.size →
      (re.regions[i]!).lo ≤ (re.regions[i]!).hi)
    (hcode : ∀ i, i < re.regions.size → (re.regions[i]!).hi ≤ re.code.size)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hshape : ∀ j, j < re.regions.size →
      ShapeOk re (regionKids re.regions).1 (regionKids re.regions).2 j) :
    ∀ (k i : Nat), re.regions.size - i ≤ k → i < re.regions.size →
      ∀ q, (re.regions[i]!).lo ≤ q → q < (re.regions[i]!).hi → RepCodeOk re q := by
  intro k
  induction k with
  | zero =>
      intro i hk hi q _ _
      omega
  | succ k ih =>
      intro i hk hi q h1 h2
      have hpos : 0 < re.regions.size := by omega
      have hqc : q < re.code.size := by have := hcode i hi; omega
      have hkid : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ∀ q', (re.regions[c]!).lo ≤ q' → q' < (re.regions[c]!).hi →
            RepCodeOk re q' := by
        intro c hP hne
        rcases hP with rfl | ⟨hic, hcs, -⟩
        · exact absurd rfl hne
        · exact fun q' g1 g2 => ih c (by omega) hcs q' g1 g2
      have hkid' : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ∀ q', (re.regions[c]!).lo ≤ q' → q' < (re.regions[c]!).hi →
            (q' < re.code.size → RepCodeOk re q') :=
        fun c hP hne q' g1 g2 _ => hkid c hP hne q' g1 g2
      have hsib : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          ChildOf re.regions i ((regionKids re.regions).2[c]!) :=
        fun c hP hne => regionKids_next hpos hord i c hP hne
      have hfirst : ChildOf re.regions i ((regionKids re.regions).1[i]!) :=
        regionKids_first hpos hord i hi
      have hloose : ∀ q' : Nat, (re.code[q']!).op.loose = true →
          (q' < re.code.size → RepCodeOk re q') :=
        fun q' hl hq' => RepCodeOk.ofLoose hlast hq' hl
      have hsh := hshape i hi
      unfold ShapeOk at hsh
      by_cases hkalt : (re.regions[i]!).kind = .alt
      · rw [hkalt] at hsh
        dsimp only at hsh
        have hfne := shapeAlt_first_ne hsh
        rw [shapeAlt] at hsh
        exact shapeAltGo_rep_ok hlast (hends i hi (Or.inl hkalt))
          (ChildOf re.regions i) hsib
          (fun c hP hne => by
            rcases hP with rfl | ⟨-, hcs, -⟩
            · exact absurd rfl hne
            · exact hrange c hcs)
          hkid re.regions.size (re.regions[i]!).lo
          ((regionKids re.regions).1[i]!) 0 hfirst hsh hfne q h1 h2
      by_cases hkrep : (re.regions[i]!).kind = .«repeat»
      · rw [hkrep] at hsh
        dsimp only at hsh
        have hhi := hends i hi (Or.inr hkrep)
        rcases shapeRepeat_head hsh with hsp | hz
        · obtain ⟨hlt, harms, hbody⟩ := shapeRepeat_opt hsp hsh
          by_cases hq0 : q = (re.regions[i]!).lo
          · subst hq0
            rcases harms with ⟨a, b⟩ | ⟨a, b⟩
            · exact repCodeOk_split hlast hqc hsp a b ⟨by omega, by omega⟩
                ⟨by omega, by omega⟩
            · exact repCodeOk_split hlast hqc hsp a b ⟨by omega, by omega⟩
                ⟨by omega, by omega⟩
          · rw [shapeSpan] at hbody
            exact shapeSpanGo_covers hloose (ChildOf re.regions i) hsib hkid'
              ((re.regions[i]!).hi - ((re.regions[i]!).lo + 1))
              ((re.regions[i]!).lo + 1) ((regionKids re.regions).1[i]!) hfirst
              (by omega) hbody q (by omega) h2 hqc
        · obtain ⟨h4, hwhich, hloopop, hlooparg, henterop, henterarg, htailop,
            htailarg, hhead, hbody, hafter, hspan⟩ := shapeRepeat_counted hz hsh
          by_cases hq0 : q = (re.regions[i]!).lo ∨ q = (re.regions[i]!).lo + 1 ∨
              q = (re.regions[i]!).lo + 2 ∨ q = (re.regions[i]!).hi - 1
          · exact repCodeOk_header hlast hhi h4 hwhich hz rfl hloopop hlooparg
              henterop henterarg htailop htailarg hhead hbody hafter hq0
          · simp only [not_or] at hq0
            rw [shapeSpan] at hspan
            exact shapeSpanGo_covers hloose (ChildOf re.regions i) hsib hkid'
              ((re.regions[i]!).hi - 1 - ((re.regions[i]!).lo + 3))
              ((re.regions[i]!).lo + 3) ((regionKids re.regions).1[i]!) hfirst
              (by omega) hspan q (by omega) (by omega) hqc
      · have hkind : (re.regions[i]!).kind = .root ∨
            (re.regions[i]!).kind = .group ∨ (re.regions[i]!).kind = .branch := by
          cases hk2 : (re.regions[i]!).kind
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd hk2 hkalt
          · exact absurd hk2 hkrep
        have hspan : shapeSpan re.code re.regions (regionKids re.regions).2
            (re.regions[i]!).lo (re.regions[i]!).hi
            (regionKids re.regions).1[i]! = .crOk := by
          rcases hkind with hk | hk | hk <;> (rw [hk] at hsh; exact hsh)
        rw [shapeSpan] at hspan
        exact shapeSpanGo_covers hloose (ChildOf re.regions i) hsib hkid'
          ((re.regions[i]!).hi - (re.regions[i]!).lo) (re.regions[i]!).lo
          ((regionKids re.regions).1[i]!) hfirst (by omega) hspan q h1 h2 hqc

/-! ## A whole accepted program -/

/-- The tree induction run at the root, whose range is the code.

Two hypotheses do work `cert_shape` does not do, and they are the two the
forward pricing already stated: that no alternation and no repeat region ends
the program, so a closing jump and a skipped body never leave the code; and
that the program's last instruction is an `Accept`, so a fall-through never
does either. The counted repetitions need neither — their targets are read off
the record, which `shape_repeat` has pinned inside the region. -/
theorem rep_code_ok_of_shape {re : Re} (hshape : certShape re = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) :
    ∀ q, q < re.code.size → RepCodeOk re q := by
  obtain ⟨hpos, -, hlo0, hhi0⟩ := certShape_root hshape
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape)
  intro q hq
  exact region_rep_code_ok
    (fun i g1 g2 => (certShape_facts hshape i g1 g2).1)
    (region_lo_le hshape)
    (fun i g => region_hi_le hshape re.regions.size i (by omega) g)
    hends hlast (fun j hj => hsh j (Nat.zero_le _) (by omega))
    re.regions.size 0 (by omega) hpos q (by omega) (by omega)

/-- And the same off an accepted certificate, which is what the callers hold.
Only its shape half is read: the prices say nothing about the layout. -/
theorem rep_code_ok_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) :
    ∀ q, q < re.code.size → RepCodeOk re q :=
  rep_code_ok_of_shape (certCheck_bt_spec hcert).2.2.2.2.1 hends hlast

/-- Forwardness including the repetition targets, which is what `repCostAt`
runs on. -/
theorem rep_fwd_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) :
    ∀ q, q < re.code.size → RepFwd re q :=
  fun q hq => (rep_code_ok_of_cert hcert hends hlast q hq).fwd

/-- Every repetition opcode belongs to its own repetition's range. A walk that
has left that range never reads the counter again, which is the fact section
4.4's measure turns on. -/
theorem rep_inside_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (q : Nat)
    (hq : q < re.code.size)
    (hop : (re.code[q]!).op = .repZero ∨ (re.code[q]!).op = .repLoop ∨
      (re.code[q]!).op = .repEnter ∨ (re.code[q]!).op = .repNext) :
    (re.code[q]!).arg < re.reps.size ∧
      (re.reps[(re.code[q]!).arg]!).head - 1 ≤ q ∧
      q < (re.reps[(re.code[q]!).arg]!).after :=
  let h := (rep_code_ok_of_cert hcert hends hlast q hq).ranged hop
  ⟨h.1, h.inside.1, h.inside.2⟩

/-- And two of them naming the same repetition are inside one range, because
that range is read off the repetition index alone. -/
theorem rep_same_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) {q q' : Nat}
    (hq : q < re.code.size) (hq' : q' < re.code.size)
    (hop : (re.code[q]!).op = .repZero ∨ (re.code[q]!).op = .repLoop ∨
      (re.code[q]!).op = .repEnter ∨ (re.code[q]!).op = .repNext)
    (hop' : (re.code[q']!).op = .repZero ∨ (re.code[q']!).op = .repLoop ∨
      (re.code[q']!).op = .repEnter ∨ (re.code[q']!).op = .repNext)
    (harg : (re.code[q']!).arg = (re.code[q]!).arg) :
    (re.reps[(re.code[q]!).arg]!).head - 1 ≤ q ∧
      q < (re.reps[(re.code[q]!).arg]!).after ∧
      (re.reps[(re.code[q]!).arg]!).head - 1 ≤ q' ∧
      q' < (re.reps[(re.code[q]!).arg]!).after := by
  obtain ⟨-, ha, hb⟩ := rep_inside_of_cert hcert hends hlast q hq hop
  obtain ⟨-, ha', hb'⟩ := rep_inside_of_cert hcert hends hlast q' hq' hop'
  rw [harg] at ha' hb'
  exact ⟨ha, hb, ha', hb'⟩

/-- The head a `RepNext` names reads back as a `RepLoop` naming the same
repetition, and a `RepLoop` is its own repetition's head with the body one
past it. -/
theorem rep_head_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) (q : Nat)
    (hq : q < re.code.size) :
    ((re.code[q]!).op = .repNext →
        (re.code[(re.reps[(re.code[q]!).arg]!).head]!).op = .repLoop ∧
          (re.code[(re.reps[(re.code[q]!).arg]!).head]!).arg = (re.code[q]!).arg) ∧
      ((re.code[q]!).op = .repLoop →
        q = (re.reps[(re.code[q]!).arg]!).head ∧
          (re.reps[(re.code[q]!).arg]!).body = q + 1) :=
  ⟨(rep_code_ok_of_cert hcert hends hlast q hq).head,
    (rep_code_ok_of_cert hcert hends hlast q hq).loop⟩

/-- A counted repeat region is its record's range: the `RepZero` one before
the head, and the exit. So the three offsets pin a repetition index to one
region. -/
theorem counted_region_range {re : Re} (hshape : certShape re = .crOk) (i : Nat)
    (hi : i < re.regions.size) (hkind : (re.regions[i]!).kind = .«repeat»)
    (hz : (re.code[(re.regions[i]!).lo]!).op = .repZero) :
    (re.regions[i]!).lo =
        (re.reps[(re.code[(re.regions[i]!).lo]!).arg]!).head - 1 ∧
      (re.regions[i]!).hi =
        (re.reps[(re.code[(re.regions[i]!).lo]!).arg]!).after := by
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape) i
    (Nat.zero_le _) (by omega)
  unfold ShapeOk at hsh
  rw [hkind] at hsh
  dsimp only at hsh
  obtain ⟨-, -, -, -, -, -, -, -, hhead, -, hafter, -⟩ := shapeRepeat_counted hz hsh
  omega

/-- And so no two repeat regions share a repetition index. -/
theorem counted_regions_agree {re : Re} (hshape : certShape re = .crOk)
    {i i' : Nat} (hi : i < re.regions.size) (hi' : i' < re.regions.size)
    (hkind : (re.regions[i]!).kind = .«repeat»)
    (hkind' : (re.regions[i']!).kind = .«repeat»)
    (hz : (re.code[(re.regions[i]!).lo]!).op = .repZero)
    (hz' : (re.code[(re.regions[i']!).lo]!).op = .repZero)
    (harg : (re.code[(re.regions[i']!).lo]!).arg =
      (re.code[(re.regions[i]!).lo]!).arg) :
    (re.regions[i]!).lo = (re.regions[i']!).lo ∧
      (re.regions[i]!).hi = (re.regions[i']!).hi := by
  obtain ⟨hlo, hhi⟩ := counted_region_range hshape i hi hkind hz
  obtain ⟨hlo', hhi'⟩ := counted_region_range hshape i' hi' hkind' hz'
  rw [harg] at hlo' hhi'
  omega

end Pcrevera.Ref
