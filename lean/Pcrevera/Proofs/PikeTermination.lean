import Pcrevera.Ref.Pike
import Pcrevera.Ref.Poly

/-!
# The Pike loops halt on their declared fuel (R-5, Pike half)

Every fueled loop on the lockstep path runs on fuel that is bookkeeping,
not a bound. This file proves it as congruence, the useful form of
termination for a fueled function: any two fuels covering the loop's own
variant give the same answer, and the fuel each call site passes covers
its variant, so the fuel expression a definition happens to pass is
sufficient and never load-bearing — the fallback a loop answers on fuel
zero never decides a result.

The variant shared by the three worklist loops — the closure of `pikeAdd`,
the scan of `scanFirst`, the emptiness probe of `pikeHollow` — is
`worklist + 2 * unmarked`: an iteration either pops an already-visited
entry, paying one from the worklist, or marks a fresh pc and pushes at
most two continuations, paying two from the unvisited count against the
pushes. A pc outside the program cannot be marked, but it also cannot
push: the two scans test the range before expanding, and the closure loop
reads the out-of-range pc as the default instruction, a `chr`, which
parks and pushes nothing. That is why the congruence needs the visited
set to be exactly as long as the program and nothing else about the
state.

`pikeLoop` is simpler — it moves one position per recursion and stops at
the subject's end — and `boundPowGo` is arithmetic: past the degenerate
bases the accumulator at least doubles per multiplication while `ok`
holds, `satMul`'s pre-check flags the overflow before the product passes
`counterMax`, and a flagged accumulator returns on any fuel at all, so 54
units always cover the loop that `boundPow` feeds 55.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- What a closure build may still mark: the false entries of the visited
set. The termination measures weigh one twice, because marking a pc buys
at most two pushes. -/
def unmarked (seen : Array Bool) : Nat := Array.countP (fun b => !b) seen

theorem unmarked_le_size (seen : Array Bool) : unmarked seen ≤ seen.size :=
  Array.countP_le_size

theorem unmarked_set_le (seen : Array Bool) (pc : Nat) :
    unmarked (seen.set! pc true) ≤ unmarked seen := by
  unfold unmarked
  rw [Array.set!_eq_setIfInBounds, ← Array.countP_toList, ← Array.countP_toList,
    Array.toList_setIfInBounds]
  rcases Nat.lt_or_ge pc seen.toList.length with hpc | hpc
  · rw [List.countP_set hpc]
    simp
  · rw [List.set_eq_of_length_le hpc]
    exact Nat.le_refl _

theorem unmarked_set_lt {seen : Array Bool} {pc : Nat} (hpc : pc < seen.size)
    (hfalse : seen[pc]! = false) :
    unmarked (seen.set! pc true) + 1 = unmarked seen := by
  unfold unmarked
  rw [Array.set!_eq_setIfInBounds, ← Array.countP_toList, ← Array.countP_toList,
    Array.toList_setIfInBounds]
  have hl : pc < seen.toList.length := by simpa using hpc
  have hg : seen.toList[pc] = false := by
    rw [Array.getElem_toList hpc]
    rw [getElem!_pos seen pc hpc] at hfalse
    exact hfalse
  have hpos : 0 < List.countP (fun b => !b) seen.toList :=
    List.countP_pos_iff.2 ⟨seen.toList[pc], List.getElem_mem hl, by rw [hg]; rfl⟩
  rw [List.countP_set hl, hg]
  show List.countP (fun b => !b) seen.toList - 1 + 0 + 1 =
    List.countP (fun b => !b) seen.toList
  omega

/-! The closure loop's helpers and what they do to the two fields the
variant reads: only `pikeDefer` touches the stack, one push, and none of
them touch the visited set. Each lemma reads its contract off the code,
on the `ok` path only — a refusal ends the loop and needs no measure. -/

theorem pikeDefer_ok {st st' : PikeSt} {pc h : Nat} {lim : Limits}
    (hok : pikeDefer st pc h lim = .ok st') :
    st'.stk = st.stk.push ⟨pc, h⟩ ∧ st'.seen = st.seen := by
  unfold pikeDefer at hok
  split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩

theorem pikeDrop_ok {st st' : PikeSt} {h : Nat} {lim : Limits}
    (hok : pikeDrop st h lim = .ok st') :
    st'.stk = st.stk ∧ st'.seen = st.seen := by
  unfold pikeDrop at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩
  · split at hok
    · split at hok
      · simp at hok
      · injection hok with hok
        subst hok
        exact ⟨rfl, rfl⟩
    · injection hok with hok
      subst hok
      exact ⟨rfl, rfl⟩

theorem pikePark_ok {st st' : PikeSt} {intoNext : Bool} {pc h : Nat}
    {lim : Limits} (hok : pikePark st intoNext pc h lim = .ok st') :
    st'.stk = st.stk ∧ st'.seen = st.seen := by
  unfold pikePark at hok
  split at hok <;> split at hok
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩
  · simp at hok
  · injection hok with hok
    subst hok
    exact ⟨rfl, rfl⟩

theorem pikeTake_fill_ok {lim : Limits} : ∀ {k : Nat} {st st' : PikeSt},
    pikeTake.fill lim k st = .ok st' →
    st'.stk = st.stk ∧ st'.seen = st.seen := by
  intro k
  induction k with
  | zero =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      injection hok with hok
      subst hok
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro st st' hok
      rw [pikeTake.fill] at hok
      split at hok
      · simp at hok
      · obtain ⟨h1, h2⟩ := ih hok
        exact ⟨h1, h2⟩

theorem pikeTake_ok {st st' : PikeSt} {novec hOut : Nat} {lim : Limits}
    (hok : pikeTake st novec lim = .ok (st', hOut)) :
    st'.stk = st.stk ∧ st'.seen = st.seen := by
  unfold pikeTake at hok
  simp only [] at hok
  split at hok
  · injection hok with hok
    injection hok with hok _
    subst hok
    exact ⟨rfl, rfl⟩
  · split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i hfill
          injection hok with hok
          injection hok with hok _
          subst hok
          obtain ⟨h1, h2⟩ := pikeTake_fill_ok hfill
          exact ⟨h1, h2⟩

theorem pikeWrite_ok {st st' : PikeSt} {novec h slot hOut : Nat}
    {value : UInt32} {lim : Limits}
    (hok : pikeWrite st novec h slot value lim = .ok (st', hOut)) :
    st'.stk = st.stk ∧ st'.seen = st.seen := by
  unfold pikeWrite at hok
  simp only [] at hok
  split at hok
  · split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i hTake
        injection hok with hok
        injection hok with hok _
        subst hok
        obtain ⟨h1, h2⟩ := pikeTake_ok hTake
        exact ⟨h1, h2⟩
  · injection hok with hok
    injection hok with hok _
    subst hok
    exact ⟨rfl, rfl⟩

/-- The closure loop of `pikeAdd` answers the same for any two fuels
strictly above `stk.size + 2 * unmarked seen`. An iteration pops one
entry; a seen pc pays the pop, a fresh pc pays two off the unvisited
count against at most two deferred continuations, and a pc outside the
program reads as the default `chr`, which parks and pushes nothing. The
only fact the argument needs from the state is that the visited set is
as long as the program — the strict inequality buys the final iteration
on the emptied stack. -/
theorem pikeAdd_go_congr (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (intoNext : Bool) (pos : Nat) :
    ∀ fuel₁ fuel₂ (st : PikeSt), st.seen.size = re.code.size →
    st.stk.size + 2 * unmarked st.seen < fuel₁ →
    st.stk.size + 2 * unmarked st.seen < fuel₂ →
    pikeAdd.go re s mo lim intoNext pos fuel₁ st =
      pikeAdd.go re s mo lim intoNext pos fuel₂ st := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ st _ h₁ _
      exact absurd h₁ (Nat.not_lt_zero _)
  | succ a ih =>
      intro fuel₂ st hsz h₁ h₂
      obtain ⟨b, rfl⟩ : ∃ b, fuel₂ = b + 1 := ⟨fuel₂ - 1, by omega⟩
      simp only [pikeAdd.go]
      split
      · rfl
      · rename_i hne
        have hstk : st.stk.size ≠ 0 := by simpa using hne
        generalize st.stk.back!.pc = pcv
        generalize st.stk.back!.h = hv
        split
        · -- The pc is already visited: the pop pays the iteration.
          split
          · rfl
          · rename_i st₂ hdrop
            obtain ⟨hk, he⟩ := pikeDrop_ok hdrop
            exact ih b _ (by rw [he]; exact hsz)
              (by rw [hk, he]; simp only [Array.size_pop]; omega)
              (by rw [hk, he]; simp only [Array.size_pop]; omega)
        · -- A fresh pc: the mark pays for the pushes.
          rename_i hseenF
          have hf : st.seen[pcv]! = false := by simpa using hseenF
          have hset_sz : (st.seen.set! pcv true).size = re.code.size := by
            rw [Array.size_set!]; exact hsz
          have hWeak := unmarked_set_le st.seen pcv
          have hStrict : re.code[pcv]!.op ≠ Op.chr →
              unmarked (st.seen.set! pcv true) + 1 = unmarked st.seen := by
            intro hno
            rcases Nat.lt_or_ge pcv re.code.size with hlt | hge
            · exact unmarked_set_lt (by omega) hf
            · exact absurd
                (by rw [getElem!_neg re.code pcv (by omega)]; rfl :
                  re.code[pcv]!.op = Op.chr) hno
          repeat' split
          all_goals first
            | rfl
            | -- forkTo: a fresh mark against two deferred continuations.
              (rename_i _stA hA _x _stB hB
               obtain ⟨hkA, heA⟩ := pikeDefer_ok hA
               obtain ⟨hkB, heB⟩ := pikeDefer_ok hB
               have hu := hStrict (by rw [‹re.code[pcv]!.op = _›]; decide)
               exact ih b _ (by rw [heB, heA]; exact hset_sz)
                 (by rw [hkB, hkA, heB, heA]
                     simp only [Array.size_push, Array.size_pop]; omega)
                 (by rw [hkB, hkA, heB, heA]
                     simp only [Array.size_push, Array.size_pop]; omega))
            | -- save: the copy-on-write, then one continuation.
              (rename_i _stW _hOut hW _x _stD hD
               obtain ⟨hkW, heW⟩ := pikeWrite_ok hW
               obtain ⟨hkD, heD⟩ := pikeDefer_ok hD
               have hu := hStrict (by rw [‹re.code[pcv]!.op = _›]; decide)
               exact ih b _ (by rw [heD, heW]; exact hset_sz)
                 (by rw [hkD, hkW, heD, heW]
                     simp only [Array.size_push, Array.size_pop]; omega)
                 (by rw [hkD, hkW, heD, heW]
                     simp only [Array.size_push, Array.size_pop]; omega))
            | -- one deferred continuation.
              (rename_i _stD hD
               obtain ⟨hk, he⟩ := pikeDefer_ok hD
               have hu := hStrict (by rw [‹re.code[pcv]!.op = _›]; decide)
               exact ih b _ (by rw [he]; exact hset_sz)
                 (by rw [hk, he]
                     simp only [Array.size_push, Array.size_pop]; omega)
                 (by rw [hk, he]
                     simp only [Array.size_push, Array.size_pop]; omega))
            | -- a dropped thread: the pop alone pays.
              (rename_i _stD hD
               obtain ⟨hk, he⟩ := pikeDrop_ok hD
               exact ih b _ (by rw [he]; exact hset_sz)
                 (by rw [hk, he]; simp only [Array.size_pop]; omega)
                 (by rw [hk, he]; simp only [Array.size_pop]; omega))
            | -- a parked thread: the pop alone pays.
              (rename_i _stD hD
               obtain ⟨hk, he⟩ := pikePark_ok hD
               exact ih b _ (by rw [he]; exact hset_sz)
                 (by rw [hk, he]; simp only [Array.size_pop]; omega)
                 (by rw [hk, he]; simp only [Array.size_pop]; omega))

/-- The fuel `pikeAdd` passes its loop is one such sufficient fuel. Every
caller arrives with an empty closure stack — `pikeAdd` itself seeds it
with the one deferred entry — so the variant is at most
`1 + 2 * code.size`, and `2 * code.size + 2` clears it strictly:
replacing that expression by anything at least as large changes nothing.
The visited-set hypothesis is the callers' state too, `pikeRun` and
`pikeLoop` sizing `seen` to the program before every build. -/
theorem pikeAdd_fuel_irrelevant (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (intoNext : Bool) (pos pc0 h0 : Nat) (st : PikeSt)
    {fuel : Nat} (hstk : st.stk.size = 0)
    (hsz : st.seen.size = re.code.size)
    (hfuel : 2 * re.code.size + 2 ≤ fuel) :
    (match pikeDefer st pc0 h0 lim with
      | .error stE => .error stE
      | .ok stO => pikeAdd.go re s mo lim intoNext pos fuel stO) =
      pikeAdd re s mo lim intoNext pos pc0 h0 st := by
  rw [pikeAdd]
  cases hdef : pikeDefer st pc0 h0 lim with
  | error stE => rfl
  | ok stO =>
      obtain ⟨hk, he⟩ := pikeDefer_ok hdef
      have hks : stO.stk.size = 1 := by
        rw [hk]; simp [hstk]
      have hus : unmarked stO.seen ≤ re.code.size := by
        rw [he, ← hsz]; exact unmarked_le_size st.seen
      exact pikeAdd_go_congr re s mo lim intoNext pos fuel _ stO
        (by rw [he]; exact hsz) (by omega) (by omega)

/-- The position loop's steps argument is a variant, not a budget: each
recursion moves `pos` up by one and the loop settles once `pos` reaches
the subject's end, so any two step counts that cover `s.size + 2 - pos`
agree. `pikeRun` passes `s.size + 2` at `pos = start`, which covers it
with room to spare. -/
theorem pikeLoop_steps_congr (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (start : Nat) (anchored : Bool) (words : Nat) :
    ∀ steps₁ steps₂ pos (st : PikeSt) (mh : Nat) (seeding matched : Bool),
    pos ≤ s.size →
    s.size + 2 - pos ≤ steps₁ → s.size + 2 - pos ≤ steps₂ →
    pikeLoop re s mo lim start anchored words steps₁ pos st mh
      seeding matched =
      pikeLoop re s mo lim start anchored words steps₂ pos st mh
        seeding matched := by
  intro steps₁
  induction steps₁ with
  | zero =>
      intro steps₂ pos st mh seeding matched hpos h₁ _
      exact absurd h₁ (by omega)
  | succ k ih =>
      intro steps₂ pos st mh seeding matched hpos h₁ h₂
      obtain ⟨l, rfl⟩ : ∃ l, steps₂ = l + 1 := ⟨steps₂ - 1, by omega⟩
      simp only [pikeLoop]
      repeat' split
      all_goals first
        | rfl
        | exact ih l (pos + 1) _ _ _ _ (by omega) (by omega) (by omega)

/-- At `pikeRun`'s call shape — the loop entered at `pos = start` within
the subject — the `s.size + 2` it passes is one sufficient step count
among equals. -/
theorem pikeLoop_steps_irrelevant (re : Re) (s : ByteArray) (mo : MOpts)
    (lim : Limits) (start : Nat) (anchored : Bool) (words : Nat)
    (st : PikeSt) (mh : Nat) (seeding matched : Bool) {steps : Nat}
    (hstart : start ≤ s.size) (hsteps : s.size + 2 ≤ steps) :
    pikeLoop re s mo lim start anchored words steps start st mh
      seeding matched =
      pikeLoop re s mo lim start anchored words (s.size + 2) start st mh
        seeding matched :=
  pikeLoop_steps_congr re s mo lim start anchored words steps (s.size + 2)
    start st mh seeding matched hstart (by omega) (by omega)

/-- `markSeen` never grows the scan variant: it refuses out-of-range and
already-marked pcs outright, and a fresh mark pays two off the unvisited
count for the one entry it pushes. The visited set keeps the program's
length either way. -/
theorem markSeen_spec (code : Array Inst) (seen : Array Bool)
    (pending : List Nat) (pc : Nat) (hsz : seen.size = code.size) :
    (markSeen code seen pending pc).1.size = code.size ∧
      (markSeen code seen pending pc).2.length +
        2 * unmarked (markSeen code seen pending pc).1 ≤
        pending.length + 2 * unmarked seen := by
  unfold markSeen
  split
  · exact ⟨hsz, Nat.le_refl _⟩
  · split
    · exact ⟨hsz, Nat.le_refl _⟩
    · rename_i hin hnew
      have hpc : pc < seen.size := by omega
      have hf : seen[pc]! = false := by simpa using hnew
      have hu := unmarked_set_lt hpc hf
      refine ⟨by rw [Array.size_set!]; exact hsz, ?_⟩
      simp only [List.length_cons]
      omega

/-- `scanFirst.go` answers the same for any two fuels covering the
worklist variant, so the conservative fuel-zero `true` never decides the
answer; `scanFirst_fuel_irrelevant` below states it at `scanFirst`'s own
seed, whose variant of at most `2 * code.size` the passed fuel
`2 * code.size + 2` covers. -/
theorem scanFirst_go_congr (code : Array Inst) (classes : Array UInt8)
    (reps : Array RepInfo) : ∀ fuel₁ fuel₂ (seen : Array Bool)
    (pending : List Nat), seen.size = code.size →
    pending.length + 2 * unmarked seen ≤ fuel₁ →
    pending.length + 2 * unmarked seen ≤ fuel₂ →
    scanFirst.go code classes reps fuel₁ (seen, pending) =
      scanFirst.go code classes reps fuel₂ (seen, pending) := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ seen pending _ h₁ _
      cases pending with
      | nil => cases fuel₂ <;> rfl
      | cons pc rest => simp [List.length_cons] at h₁
  | succ a ih =>
      intro fuel₂ seen pending hsz h₁ h₂
      cases pending with
      | nil => cases fuel₂ <;> rfl
      | cons pc rest =>
          simp only [List.length_cons] at h₁ h₂
          obtain ⟨l, rfl⟩ : ∃ l, fuel₂ = l + 1 := ⟨fuel₂ - 1, by omega⟩
          have step : ∀ fuel' (mp : Array Bool × List Nat),
              mp.1.size = code.size →
              mp.2.length + 2 * unmarked mp.1 ≤ a →
              mp.2.length + 2 * unmarked mp.1 ≤ fuel' →
              scanFirst.go code classes reps a mp =
                scanFirst.go code classes reps fuel' mp :=
            fun fuel' mp hs hm hm' => ih fuel' mp.1 mp.2 hs hm hm'
          simp only [scanFirst.go]
          repeat' split
          all_goals first
            | rfl
            | rw [ih l seen rest hsz (by omega) (by omega)]
            | (obtain ⟨hs1, hm1⟩ := markSeen_spec code seen rest _ hsz
               exact step l _ hs1 (by omega) (by omega))
            | (obtain ⟨hs1, hm1⟩ := markSeen_spec code seen rest _ hsz
               obtain ⟨hs2, hm2⟩ := markSeen_spec code _ _ _ hs1
               exact step l _ hs2 (by omega) (by omega))

/-- `scanFirst` at its own seed: any fuel from `2 * code.size + 2` up
computes the same scan. -/
theorem scanFirst_fuel_irrelevant (code : Array Inst)
    (classes : Array UInt8) (reps : Array RepInfo) {fuel : Nat}
    (hfuel : 2 * code.size + 2 ≤ fuel) :
    scanFirst.go code classes reps fuel
      (markSeen code (Array.replicate code.size false) [] 0) =
      scanFirst code classes reps := by
  rw [scanFirst]
  obtain ⟨hs, hm⟩ := markSeen_spec code (Array.replicate code.size false)
    [] 0 (by simp)
  have hu : unmarked (Array.replicate code.size false) ≤ code.size := by
    have := unmarked_le_size (Array.replicate code.size false)
    simpa using this
  simp only [List.length_nil] at hm
  exact scanFirst_go_congr code classes reps fuel (2 * code.size + 2)
    (markSeen code (Array.replicate code.size false) [] 0).1
    (markSeen code (Array.replicate code.size false) [] 0).2
    hs (by omega) (by omega)

/-- The same congruence for `pikeHollow.go`. Its pushes land before the
pushed pcs are marked, so the worklist may hold duplicates — the variant
still falls, because an iteration that marks a pc pays two off the
unvisited count against its at most two pushes, and a duplicate pops for
one off the worklist. `pikeHollow` seeds one entry under fuel
`2 * code.size + 2`, which covers the variant `1 + 2 * code.size`. -/
theorem pikeHollow_go_congr (code : Array Inst) (reps : Array RepInfo)
    (which : Nat) : ∀ fuel₁ fuel₂ (seen : Array Bool) (pending : List Nat),
    seen.size = code.size →
    pending.length + 2 * unmarked seen ≤ fuel₁ →
    pending.length + 2 * unmarked seen ≤ fuel₂ →
    pikeHollow.go code reps which fuel₁ seen pending =
      pikeHollow.go code reps which fuel₂ seen pending := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ seen pending _ h₁ _
      cases pending with
      | nil => cases fuel₂ <;> rfl
      | cons pc rest => simp [List.length_cons] at h₁
  | succ a ih =>
      intro fuel₂ seen pending hsz h₁ h₂
      cases pending with
      | nil => cases fuel₂ <;> rfl
      | cons pc rest =>
          simp only [List.length_cons] at h₁ h₂
          obtain ⟨l, rfl⟩ : ∃ l, fuel₂ = l + 1 := ⟨fuel₂ - 1, by omega⟩
          simp only [pikeHollow.go]
          split
          · rfl
          · split
            · rfl
            · split
              · exact ih l seen rest hsz (by omega) (by omega)
              · rename_i hge hafter hseen
                have hf : seen[pc]! = false := by simpa using hseen
                have hu := unmarked_set_lt (show pc < seen.size by omega) hf
                have hs' : (seen.set! pc true).size = code.size := by
                  rw [Array.size_set!]; exact hsz
                split
                all_goals
                  exact ih l _ _ hs'
                    (by (try simp only [List.length_cons]); omega)
                    (by (try simp only [List.length_cons]); omega)

/-- `pikeHollow` at its own seed: any fuel from `2 * code.size + 2` up
gives the same verdict. -/
theorem pikeHollow_fuel_irrelevant (code : Array Inst)
    (reps : Array RepInfo) (which : Nat) {fuel : Nat}
    (hfuel : 2 * code.size + 2 ≤ fuel) :
    pikeHollow.go code reps which fuel (Array.replicate code.size false)
      [(reps[which]!).body] = pikeHollow code reps which := by
  rw [pikeHollow]
  have hu : unmarked (Array.replicate code.size false) ≤ code.size := by
    have := unmarked_le_size (Array.replicate code.size false)
    simpa using this
  exact pikeHollow_go_congr code reps which fuel (2 * code.size + 2) _ _
    (by simp) (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- A flagged accumulator ends `boundPowGo` on any fuel at all, zero
included, so an overflow never consults the fuel. -/
theorem boundPowGo_stuck {base exp i : Nat} {out : Bound}
    (h : out.ok = false) (fuel : Nat) :
    boundPowGo base exp fuel i out = out := by
  cases fuel with
  | zero => rfl
  | succ f =>
      simp only [boundPowGo]
      exact if_neg (fun hc => Bool.noConfusion (h ▸ hc.2))

/-- One multiplication step of the power loop, for a real base and a
positive accumulator: either the pre-check flags the overflow, or the
product lands exactly and stays within the counter. -/
theorem boundMul_finite_step {base : Nat} (hbase : 2 ≤ base) {out : Bound}
    (hok : out.ok = true) (hpos : 1 ≤ out.value) :
    boundMul out (Bound.finite base) = Bound.exceeds ∨
      (boundMul out (Bound.finite base) = Bound.finite (out.value * base) ∧
        out.value * base ≤ counterMax) := by
  unfold boundMul satMul Bound.finite
  rw [hok]
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false]
  rw [if_neg (show ¬(out.value = 0 ∨ base = 0) by omega)]
  by_cases hsat : out.value > counterMax / base
  · rw [if_pos hsat]
    left
    rfl
  · rw [if_neg hsat]
    right
    exact ⟨rfl, (Nat.le_div_iff_mul_le (by omega)).1 (by omega)⟩

/-- `boundPowGo` cannot iterate more than 54 times for a base of at least
two: while `ok` holds the accumulator at least doubles per round and stays
within `counterMax = 2^53 - 1`, so at most 52 doublings succeed past the
first, the next one is flagged, and a flagged accumulator returns at once.
`j` tracks the doublings already banked: any two fuels covering `54 - j`
agree. -/
theorem boundPowGo_congr {base : Nat} (hbase : 2 ≤ base) (exp : Nat) :
    ∀ fuel₁ fuel₂ i j (out : Bound), out.ok = true →
    2 ^ j ≤ out.value → out.value ≤ counterMax →
    54 - j ≤ fuel₁ → 54 - j ≤ fuel₂ →
    boundPowGo base exp fuel₁ i out = boundPowGo base exp fuel₂ i out := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
      intro fuel₂ i j out hok hpow hle h₁ _
      exfalso
      have hp : (2 : Nat) ^ 54 ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hlt : (2 : Nat) ^ 53 < 2 ^ 54 :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      have hcm : counterMax = 2 ^ 53 - 1 := rfl
      omega
  | succ k ihk =>
      intro fuel₂ i j out hok hpow hle h₁ h₂
      have hj : j ≤ 52 := by
        rcases Nat.lt_or_ge 52 j with hgt | hle'
        · exfalso
          have hp : (2 : Nat) ^ 53 ≤ 2 ^ j :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have hpz : 0 < (2 : Nat) ^ 53 := Nat.pow_pos (by omega)
          have hcm : counterMax = 2 ^ 53 - 1 := rfl
          omega
        · exact hle'
      obtain ⟨l, rfl⟩ : ∃ l, fuel₂ = l + 1 := ⟨fuel₂ - 1, by omega⟩
      simp only [boundPowGo]
      by_cases hc : i < exp ∧ out.ok = true
      · rw [if_pos hc, if_pos hc]
        have hpz : 0 < (2 : Nat) ^ j := Nat.pow_pos (by omega)
        rcases boundMul_finite_step hbase hok (by omega) with
          hbad | ⟨heq, hlee⟩
        · rw [hbad, boundPowGo_stuck rfl, boundPowGo_stuck rfl]
        · rw [heq]
          have hpow' : 2 ^ (j + 1) ≤ out.value * base := by
            rw [Nat.pow_succ]
            exact Nat.mul_le_mul hpow hbase
          exact ihk l (i + 1) (j + 1) (Bound.finite (out.value * base)) rfl
            hpow' hlee (by omega) (by omega)
      · rw [if_neg hc, if_neg hc]

/-- The payoff at `boundPow`'s call shape: seeded with `Bound.finite 1`,
any two fuels of at least 54 agree, whatever the exponent. -/
theorem boundPowGo_fuel_irrelevant {base : Nat} (hbase : 2 ≤ base)
    (exp : Nat) {fuel₁ fuel₂ : Nat} (h₁ : 54 ≤ fuel₁) (h₂ : 54 ≤ fuel₂) :
    boundPowGo base exp fuel₁ 0 (Bound.finite 1) =
      boundPowGo base exp fuel₂ 0 (Bound.finite 1) := by
  exact boundPowGo_congr hbase exp fuel₁ fuel₂ 0 0 (Bound.finite 1) rfl
    (Nat.le_refl 1) (show (1 : Nat) ≤ counterMax by unfold counterMax; omega)
    (by omega) (by omega)

/-- So `boundPow`'s 55 is not load-bearing: from 54 up, any fuel computes
the same power. -/
theorem boundPow_eq_boundPowGo {base : Nat} (hbase : 2 ≤ base) (exp : Nat)
    {fuel : Nat} (hfuel : 54 ≤ fuel) :
    boundPow base exp = boundPowGo base exp fuel 0 (Bound.finite 1) := by
  unfold boundPow
  rw [if_neg (by omega), if_neg (by omega)]
  exact boundPowGo_fuel_irrelevant hbase exp (by omega) hfuel

end Pcrevera.Ref
