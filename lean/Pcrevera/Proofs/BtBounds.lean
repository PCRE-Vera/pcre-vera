import Pcrevera.Proofs.PolySound
import Pcrevera.Proofs.BtTermination

/-!
# What a backtracking run may spend (R-6 through R-8, the bt half)

An accepted certificate promises a caller three numbers, and BOUNDS.md
proves them in two halves. Section 4 prices one *entry* into the program by
composing the region tree; section 5 turns one entry into a whole call —
the setup, one reset and one attempt per starting position, the delivery, and
the growth of the two scratch arrays. This file is the section 5 half, from
the checker's arithmetic down to what `btRun` actually charges, with the
section 4 half entering as the hypothesis `AttemptsWithin`.

Three things live here.

`chargeCall_dom` reads the checker's whole-call arithmetic back as numbers.
On the accepted path every `polyAdd` and `polyMul` had a clean flag, so the
claimed cost dominates `setup + deliver + (n+1) * (reset + work + 4*trail) +
3*scratch` and the claimed memory dominates `setup + deliver + 2*scratch`,
with `scratch` the growth schedule's capacity for the claimed entry counts.
The stack and the trail are held to equality, which is what lets the numbers
below be stated about the certificate's own claims rather than about the
root region's.

The growth schedule is the middle of it. `chargeGrow_within` prices one step
of it against the reservation it leaves standing: the doubling is what makes
three times the final reservation cover every byte the growth ever charged,
and holding both buffers during the copy is what makes the peak twice it.
The one thing that argument needs is that the declared maximum never clamps
the schedule, and `chargeGrow_doubles` gets that from the caller's own memory
limit — reaching the maximum would mean holding the whole allocation ceiling
in one array while the buffer being copied out of sat beside it.

The run is the last of it. `Within` is the invariant the attempt loop
carries: the cost charged, amortized against the reservation so that growth
is paid for once across the call rather than once per attempt; the two
capacities; the memory identity `mem = setup + reserved`; the peak; and the
stack depth. `btLoop_within` composes it over the starting positions and
`btRun_within` adds the setup and the delivery, which is R-6, R-7 and R-8 for
this configuration.

The per-attempt half is BOUNDS.md section 4, and it enters as
`AttemptsWithin`: one entry into the program visits at most the root
region's claimed `work`, records at most its `trail` and never pushes past
its `stack`. Two cases of it are proved here rather than assumed.

Section 4.1 with no children is the first: a region tree that is the root
alone, which is a pattern with no group, no alternation and no repetition.
The checker's walk and the run then agree instruction for instruction —
`scanSpanGo_straight` reads the walk as an opcode inventory and a visit
count, `btStep_quiet` runs the VM against the same count, and
`attemptsWithin_straight` joins them.

Section 4.1 with a child is the second, and it is where the composition
actually happens: `scanSpanGo_children` walks a range that has children in
it, charging the flow times what a child claims and jumping to the child's
end, so all the parent needs to know about a child is its claim — BOUNDS.md's
"soundness is an induction one step deep", made literal. The arithmetic that
step needs is `visitCount_split` and `visitCount_stop`: a stretch with no
Accept in it splits, and one with an Accept in it stops there, which is what
lets a child that swallows the attempt cost the parent nothing afterwards.
`attemptsWithin_group` instantiates it for a root with one group inside.

The measure a deeper nest will recurse on is here as well.
`certShape_facts` reads the nesting pass back — every region comes after its
parent and sits inside its range — and `regionKids_ok` says the child lists
really hang off the region they are filed under, so `ChildOf`, the predicate
`scanSpanGo_children` carries, holds of every cursor a region's walk can
meet and every one of them has a larger index than the region walking it.
What is left for the nest is the induction that spends it: the visit bound
for a region from the bound for every region after it, walking the index
downwards.

Alternation and repetition need more than that. Each wants its own walk
(`scanAlt`, `scanRepeat`), and on the run side a richer invariant than
`Quiet`: the moment a program forks, the backtrack stack stops being empty
and the trail starts recording, which is exactly what `pushBt_within`,
`fork_within` and `writeReg_within` price and what `Within` was shaped to
carry.

One thing the checker does not ask about turns out to be load-bearing: that
the program contains an Accept. `cert_shape` admits a straight-line region of
tests with no Accept in it, and a run of one walks off the end of the code —
where the reference reads a default instruction and the real engine would
read past its own array. The theorems below take the Accept as a hypothesis
rather than pretending otherwise; the compiler emits one on every path, and
whether the checker should be refusing programs that have none is a question
for BOUNDS.md.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## The bound algebra, in the projection form a flag chain leaves behind -/

/-- A clean flag out of `polyAdd` means the flag went in clean: every step
of it only ever raises one. -/
theorem polyAdd_snd {a b : Poly} {over : Bool}
    (h : (polyAdd a b over).2 = false) : over = false := by
  simp only [polyAdd] at h
  obtain ⟨-, f3⟩ := satAdd_snd h
  obtain ⟨-, f2⟩ := satAdd_snd f3
  obtain ⟨-, f1⟩ := satAdd_snd f2
  obtain ⟨-, f0⟩ := satAdd_snd f1
  exact (satAdd_snd f0).2

/-- And then the sum it answers is worth at least the two inputs together —
at least, because it keeps the larger of the two bases. -/
theorem polyAdd_le {a b : Poly} {over : Bool}
    (h : (polyAdd a b over).2 = false) (n : Nat) :
    a.val n + b.val n ≤ (polyAdd a b over).1.val n := by
  have hp : polyAdd a b over = ((polyAdd a b over).1, (polyAdd a b over).2) := rfl
  rw [h] at hp
  exact polyAdd_sound hp n

/-- The same reading of `polyMul`'s flag. -/
theorem polyMul_snd {a b : Poly} {over : Bool}
    (h : (polyMul a b over).2 = false) : over = false := by
  simp only [polyMul] at h
  exact (satMul_snd (mulFold_flag (a := a) (b := b) (fun _ _ => rfl) _ _ h)).2

/-- A clean multiplication is exact. -/
theorem polyMul_eq {a b : Poly} {over : Bool}
    (h : (polyMul a b over).2 = false) (n : Nat) :
    (polyMul a b over).1.val n = a.val n * b.val n := by
  have hp : polyMul a b over = ((polyMul a b over).1, (polyMul a b over).2) := rfl
  rw [h] at hp
  exact polyMul_sound hp n

/-- The three bounds the section 5 arithmetic builds from. -/
theorem Poly.val_const (c n : Nat) : (Poly.const c).val n = c := by
  simp [Poly.val, Poly.part, Poly.const]

theorem Poly.val_zero (n : Nat) : Poly.zero.val n = 0 := by
  simp [Poly.val, Poly.part, Poly.zero]

theorem Poly.val_step (n : Nat) : Poly.step.val n = n + 1 := by
  simp [Poly.val, Poly.part, Poly.step]

/-- A bound with a coefficient in it is worth at least one at every length:
every basis function is at least one, and nothing in the algebra lowers a
base below one. -/
theorem Poly.val_pos {p : Poly} (hbase : 1 ≤ p.base) (h : p.nothing = false)
    (n : Nat) : 1 ≤ p.val n := by
  obtain ⟨-, -, -, hpart⟩ := polyValue_shape p n (by simp [h])
  exact Nat.mul_le_mul (Nat.one_le_pow _ _ hbase) hpart

/-- And one worth nothing really is nothing. -/
theorem Poly.val_nothing {p : Poly} (h : p.nothing = true) (n : Nat) :
    p.val n = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := nothing_iff.mp h
  simp [Poly.val, Poly.part, h0, h1, h2, h3, h4]

/-! ## The section 5 numbers -/

/-- BOUNDS.md section 5's `capacity(x)`: nothing for an array nothing ever
pushed to, else what a run doubling from four ends up holding. -/
def capacityOf (entries : Nat) : Nat :=
  if entries = 0 then 0 else growMin + growFactor * entries

/-- The same schedule as a bound, which is `charge_call`'s local `grow`
before it weighs the capacity by an entry size. It is written out here so
the whole-call proof can name it rather than carry the expression. -/
def growCapacity (claimed : Poly) (over : Bool) : Poly × Bool :=
  if !claimed.nothing then
    let (grown, over) := polyMul claimed (Poly.const growFactor) over
    polyAdd (Poly.const growMin) grown over
  else (Poly.zero, over)

/-- The shape a flag chain leaves it in. -/
theorem growCapacity_unfold (claimed : Poly) (over : Bool) :
    growCapacity claimed over =
      if !claimed.nothing then
        polyAdd (Poly.const growMin) (polyMul claimed (Poly.const growFactor) over).1
          (polyMul claimed (Poly.const growFactor) over).2
      else (Poly.zero, over) := rfl

/-- Its flag, read the same way as the others. -/
theorem growCapacity_snd {claimed : Poly} {over : Bool}
    (h : (growCapacity claimed over).2 = false) : over = false := by
  rw [growCapacity_unfold] at h
  split at h
  · exact polyMul_snd (polyAdd_snd h)
  · exact h

/-- And what it is worth: at least the growth schedule's capacity for the
claimed entry count. A claim worth nothing reserves nothing, which is the
case the `nothing` test is there for. -/
theorem growCapacity_dom {claimed : Poly} {over : Bool} (hbase : 1 ≤ claimed.base)
    (h : (growCapacity claimed over).2 = false) (n : Nat) :
    capacityOf (claimed.val n) ≤ (growCapacity claimed over).1.val n := by
  rw [growCapacity_unfold] at h ⊢
  split at h
  · rename_i hn
    rw [Bool.not_eq_true'] at hn
    rw [if_pos (by simp [hn])]
    have hv := polyAdd_le h n
    have hm := polyMul_eq (polyAdd_snd h) n
    have hpos := Poly.val_pos hbase hn n
    rw [Poly.val_const] at hv hm
    unfold capacityOf
    rw [if_neg (by omega)]
    simp only [growMin, growFactor] at *
    omega
  · rename_i hn
    have hn' : claimed.nothing = true := by simpa using hn
    rw [if_neg (by simp [hn']), Poly.val_nothing hn', Poly.val_zero, capacityOf,
      if_pos rfl]
    exact Nat.le_refl 0

/-- The register file and the ovector, zeroed once. -/
def btSetup (re : Re) : Nat := (re.nregs + re.novec) * regSize

/-- The ovector copied back out, once, on a match. -/
def btDeliver (re : Re) : Nat := re.novec * regSize

/-- The registers cleared again at every starting position. -/
def btReset (re : Re) : Nat := re.nregs * regSize

/-- The scratch reservation of BOUNDS.md section 5: the growth schedule's
capacity for each array, weighed by its entry size. -/
def btScratch (stack trail : Nat) : Nat :=
  capacityOf stack * btSize + capacityOf trail * undoSize

/-- `charge_call`, read as numbers. An accepted whole-call claim dominates
the section 5 equations at every subject length, and the stack and the trail
are the root region's claims exactly — the equalities the checker holds them
to, which is what lets a caller read the certificate's own fields below. -/
theorem chargeCall_dom {re : Re} {cert : Cert} {whole : Price} {over : Bool}
    (hs : 1 ≤ whole.stack.base) (ht : 1 ≤ whole.trail.base)
    (h : (chargeCall re cert whole over).1 = .crOk) (n : Nat) :
    btSetup re + btDeliver re
        + ((n + 1) * (btReset re + (whole.work.val n + regSize * whole.trail.val n))
          + 3 * btScratch (whole.stack.val n) (whole.trail.val n)) ≤ cert.cost.val n ∧
      btSetup re + btDeliver re
        + 2 * btScratch (whole.stack.val n) (whole.trail.val n) ≤ cert.mem.val n ∧
      cert.stack = whole.stack ∧ cert.trail = whole.trail := by
  simp only [chargeCall] at h
  simp only [← growCapacity_unfold] at h
  split at h
  · exact absurd h (by simp)
  rename_i hover
  rw [Bool.not_eq_true] at hover
  split at h
  · exact absurd h (by simp)
  rename_i hcost
  split at h
  · exact absurd h (by simp)
  rename_i hstack
  split at h
  · exact absurd h (by simp)
  rename_i htrail
  split at h
  · exact absurd h (by simp)
  rename_i hmem
  rw [Bool.not_eq_true, Bool.not_eq_false'] at hcost hstack htrail hmem
  -- The flag chain, read back to front: a clean flag at the end means every
  -- step of the section 5 arithmetic was exact.
  have f13 := polyAdd_snd hover
  have f12 := polyMul_snd f13
  have f11 := polyAdd_snd f12
  have f10 := polyAdd_snd f11
  have f9 := polyMul_snd f10
  have f8 := polyMul_snd f9
  have f7 := polyAdd_snd f8
  have f6 := polyAdd_snd f7
  have f5 := polyMul_snd f6
  have f4 := polyAdd_snd f5
  have f3 := polyMul_snd f4
  have f2 := growCapacity_snd f3
  have f1 := polyAdd_snd f2
  have f0 := polyMul_snd f1
  -- What each step is worth at this subject length.
  have vcapS := growCapacity_dom hs f0 n
  have vwS := polyMul_eq f1 n
  have vs1 := polyAdd_le f2 n
  have vcapT := growCapacity_dom ht f3 n
  have vwT := polyMul_eq f4 n
  have vs2 := polyAdd_le f5 n
  have vreplay := polyMul_eq f6 n
  have vreplayed := polyAdd_le f7 n
  have vattempt := polyAdd_le f8 n
  have vpositions := polyMul_eq f9 n
  have vgrowth := polyMul_eq f10 n
  have vrunning := polyAdd_le f11 n
  have vcostp := polyAdd_le f12 n
  have vheld := polyMul_eq f13 n
  have vmemp := polyAdd_le hover n
  rw [Poly.val_const] at vwS vwT vreplay vattempt vgrowth vcostp vheld vmemp
  rw [Poly.val_step] at vpositions
  rw [Poly.val_zero] at vs1
  simp only [btSetup, btDeliver, btReset, btScratch, Re.novec, regSize, btSize,
    undoSize] at *
  refine ⟨?_, ?_, polyEq_eq hstack, polyEq_eq htrail⟩
  · refine Nat.le_trans ?_ (polyGe_sound hcost n)
    refine Nat.le_trans ?_ vcostp
    refine Nat.add_le_add (by omega) ?_
    refine Nat.le_trans ?_ vrunning
    refine Nat.add_le_add ?_ ?_
    · rw [vpositions, Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (by omega)
    · rw [vgrowth, Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.le_trans (by omega) vs2)
  · refine Nat.le_trans ?_ (polyGe_sound hmem n)
    refine Nat.le_trans ?_ vmemp
    refine Nat.add_le_add (by omega) ?_
    rw [vheld, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.le_trans (by omega) vs2)

/-- A tree with no regions in it is refused before anything is priced, so
an accepted program has a root to read prices off. -/
theorem certShape_regions_pos {re : Re} (h : certShape re = .crOk) :
    0 < re.regions.size := by
  simp only [certShape] at h
  split at h
  · exact absurd h (by decide)
  · omega

/-- The base rule at the root: the first price named a growth base, and a
base that is not zero is at least one. -/
theorem certCheckBases_head {prices : Array Price} {fuel : Nat}
    (h : certCheckBases prices 0 (fuel + 1) = true) :
    1 ≤ (prices[0]!).work.base ∧ 1 ≤ (prices[0]!).outs.base ∧
      1 ≤ (prices[0]!).stack.base ∧ 1 ≤ (prices[0]!).trail.base := by
  rw [certCheckBases] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne
    simp only [not_or] at hne
    omega

/-- `cert_check` on the backtracking configuration, with the dispatch and
the bindings taken out: the same decisions in the same order, so the
extraction below can read them off one at a time. -/
theorem certCheck_bt_unfold (re : Re) (cert : Cert) :
    certCheck re .backtrack cert =
      if cert.config ≠ .backtrack then .crConfig
      else if certShape re ≠ .crOk then certShape re
      else if cert.prices.size ≠ re.regions.size then .crPrices
      else if cert.cost.base = 0 ∨ cert.stack.base = 0 ∨
          cert.trail.base = 0 ∨ cert.mem.base = 0 then .crBase
      else if cert.complexity = .linear ∧ !cert.cost.linear then .crNotLinear
      else if !certCheckBases cert.prices 0 re.regions.size then .crBase
      else
        let (kids, sibs) := regionKids re.regions
        let (verdict, over) :=
          certCheckRegions re cert.prices kids sibs 0 re.regions.size false
        if verdict ≠ .crOk then verdict
        else
          let (charged, _) := chargeCall re cert (cert.prices[0]!) over
          if charged ≠ .crOk then charged else .crOk := rfl

/-- What an accepted backtracking certificate carries: the two claims the
whole-call arithmetic is priced from name a growth base, and `charge_call`
accepted the totals. -/
theorem certCheck_bt_spec {re : Re} {cert : Cert}
    (h : certCheck re .backtrack cert = .crOk) :
    1 ≤ (cert.prices[0]!).stack.base ∧ 1 ≤ (cert.prices[0]!).trail.base ∧
      (∃ over : Bool, (chargeCall re cert (cert.prices[0]!) over).1 = .crOk) ∧
      certShape re = .crOk ∧
      (∃ over : Bool, certCheckRegions re cert.prices
        (regionKids re.regions).1 (regionKids re.regions).2 0 re.regions.size
        false = (.crOk, over)) := by
  rw [certCheck_bt_unfold] at h
  repeat (split at h <;> try (first
    | exact absurd h (by decide)
    | (rename_i hx; exact absurd hx (by decide))
    | (rename_i hx; exact absurd rfl hx)
    | (rename_i hx; exact absurd h hx)))
  rename_i hcfg hshape hsize hbase hlin hbases xa kids sibs hkids xb verdict over
    hregions hv xc charged flag hcharge hok
  have hpos : 0 < re.regions.size := certShape_regions_pos (by simpa using hshape)
  obtain ⟨fuel, hfuel⟩ : ∃ f, re.regions.size = f + 1 :=
    ⟨re.regions.size - 1, by omega⟩
  rw [hfuel] at hbases
  obtain ⟨-, -, hst, htr⟩ := certCheckBases_head (by simpa using hbases)
  have hverdict : verdict = Cr.crOk := by simpa using hv
  rw [hverdict] at hregions
  refine ⟨hst, htr, ⟨over, by rw [hcharge]; simpa using hok⟩,
    by simpa using hshape, over, ?_⟩
  rw [hkids]
  exact hregions

/-! ## What a run of the certified program does -/

/-- The scratch bytes a run holds: the two growing arrays at their
capacities. Growth is charged against this, and the whole call pays at most
three times it. -/
def BtSt.reserved (st : BtSt) : Nat :=
  st.btCap * btSize + st.trailCap * undoSize

/-- The state a whole call ends in, whichever way it ended. -/
def RunEnd.state : RunEnd → BtSt
  | .matched st => st
  | .noMatch st => st
  | .exceeded st => st

/-- A stretch of a run staying inside the prices a certificate names: it
charges at most `spent` on top of the growth its own reservation pays for,
it reserves no more than the growth schedule's capacity for the claimed
entry counts, its memory peak stays under the section 5 reservation, and
the backtrack stack never gets deeper than the claim.

The cost line is amortized on purpose. Growth is charged once across the
call rather than once per attempt, and the schedule doubles, so a stretch
that grows an array from `c` to `2c` entries pays `3c` entry-widths and
leaves three times the new reservation standing behind it. Carrying the
reservation on both sides of the inequality is what lets the attempts
compose without counting the growth twice. -/
structure Within (setup stack trail spent : Nat) (st out : BtSt) : Prop where
  charged : out.m.cost + 3 * st.reserved ≤ st.m.cost + 3 * out.reserved + spent
  btRoom : out.btCap ≤ capacityOf stack
  trailRoom : out.trailCap ≤ capacityOf trail
  held : out.m.mem = setup + out.reserved
  resident : out.m.peak ≤ max st.m.peak (setup + 2 * btScratch stack trail)
  deepest : out.stackpeak ≤ max st.stackpeak stack

/-- Standing still is inside any price. -/
theorem Within.rfl {setup stack trail : Nat} {st : BtSt}
    (hbt : st.btCap ≤ capacityOf stack) (htr : st.trailCap ≤ capacityOf trail)
    (hmem : st.m.mem = setup + st.reserved) :
    Within setup stack trail 0 st st :=
  ⟨by omega, hbt, htr, hmem, by omega, by omega⟩

/-- Two stretches in a row spend what the two of them spend, and the
reservation in the middle cancels — which is the point of carrying it. -/
theorem Within.trans {setup stack trail a b : Nat} {st mid out : BtSt}
    (h₁ : Within setup stack trail a st mid)
    (h₂ : Within setup stack trail b mid out) :
    Within setup stack trail (a + b) st out := by
  obtain ⟨c₁, -, -, -, p₁, d₁⟩ := h₁
  obtain ⟨c₂, r₂, t₂, m₂, p₂, d₂⟩ := h₂
  exact ⟨by omega, r₂, t₂, m₂, by omega, by omega⟩

/-- A stretch inside one price is inside any larger one. -/
theorem Within.mono {setup stack trail a b : Nat} {st out : BtSt}
    (h : Within setup stack trail a st out) (hle : a ≤ b) :
    Within setup stack trail b st out :=
  ⟨by have := h.charged; omega, h.btRoom, h.trailRoom, h.held, h.resident,
    h.deepest⟩

/-- A charge that moves nothing else: one instruction visit at a unit, or
the replay a backtrack pop pays for before it puts the registers back. -/
theorem Within.charge {setup stack trail : Nat} {st : BtSt} (c : Nat)
    (hbt : st.btCap ≤ capacityOf stack) (htr : st.trailCap ≤ capacityOf trail)
    (hmem : st.m.mem = setup + st.reserved) :
    Within setup stack trail c st
      { st with m := { st.m with cost := st.m.cost + c } } := by
  refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;> (dsimp only [BtSt.reserved] at hmem ⊢) <;>
    omega

/-- Every attempt of a run stays inside the root region's prices: one entry
into the program visits at most `work` instructions and records at most
`trail` undo entries, the replay a pop charges is one register width per
undo entry, and the stack never passes `stack` entries.

This is the per-attempt half of BOUNDS.md section 4, which the composition
below takes as given. -/
def AttemptsWithin (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start setup stack trail work : Nat) : Prop :=
  ∀ (attempt fuel : Nat) (st : BtSt), st.bt = #[] → st.trail = #[] →
    st.btCap ≤ capacityOf stack → st.trailCap ≤ capacityOf trail →
    st.m.mem = setup + st.reserved →
    Within setup stack trail (work + regSize * trail) st
      (btStep re s mo lim start attempt fuel 0 attempt st).state

/-- One turn of the attempt loop, with the bindings taken out: the reset
charged, the arrays truncated capacity-in-hand, and the attempt run on the
budget that is left. -/
theorem btLoop_succ (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start steps attempt : Nat) (st : BtSt) :
    btLoop re s mo lim start (steps + 1) attempt st =
      if re.nregs * regSize > lim.cost - st.m.cost then .exceeded st
      else
        match btStep re s mo lim start attempt
            (lim.cost + 1 - (st.m.cost + re.nregs * regSize)) 0 attempt
            ⟨Array.replicate re.nregs unset32, #[], st.btCap, #[], st.trailCap,
              ⟨st.m.cost + re.nregs * regSize, st.m.mem, st.m.peak⟩,
              st.stackpeak⟩ with
        | .found _ st => .matched st
        | .exceeded st => .exceeded st
        | .exhausted st =>
            if re.anchored || mo.anchored || attempt ≥ s.size then .noMatch st
            else
              btLoop re s mo lim start steps
                (if re.skipsAttempt s (attempt + 1) then attempt + 1 + 1
                  else attempt + 1) st := rfl

/-- The attempt loop composes: `steps` starting positions cost `steps`
resets and `steps` attempts, and the growth stays charged once. -/
theorem btLoop_within {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start setup stack trail work : Nat}
    (hatt : AttemptsWithin re s mo lim start setup stack trail work) :
    ∀ (steps attempt : Nat) (st : BtSt), st.btCap ≤ capacityOf stack →
      st.trailCap ≤ capacityOf trail → st.m.mem = setup + st.reserved →
      Within setup stack trail
        (steps * (btReset re + (work + regSize * trail))) st
        (btLoop re s mo lim start steps attempt st).state := by
  intro steps
  induction steps with
  | zero =>
      intro attempt st hbt htr hmem
      rw [btLoop]
      exact (Within.rfl hbt htr hmem).mono (Nat.zero_le _)
  | succ steps ih =>
      intro attempt st hbt htr hmem
      rw [btLoop_succ, Nat.succ_mul]
      split
      · exact (Within.rfl hbt htr hmem).mono (Nat.zero_le _)
      · have hstep := hatt attempt
          (lim.cost + 1 - (st.m.cost + re.nregs * regSize))
          ⟨Array.replicate re.nregs unset32, #[], st.btCap, #[], st.trailCap,
            ⟨st.m.cost + re.nregs * regSize, st.m.mem, st.m.peak⟩,
            st.stackpeak⟩ rfl rfl hbt htr (by simpa only [BtSt.reserved] using hmem)
        split
        · rename_i endPos st' hout
          rw [hout] at hstep
          simp only [AttemptOut.state] at hstep
          obtain ⟨c, r, t, hm, p, d⟩ := hstep
          simp only [BtSt.reserved, btReset] at c ⊢
          refine ⟨?_, r, t, hm, ?_, ?_⟩ <;>
            (try simp only [RunEnd.state, BtSt.reserved]) <;> omega
        · rename_i st' hout
          rw [hout] at hstep
          simp only [AttemptOut.state] at hstep
          obtain ⟨c, r, t, hm, p, d⟩ := hstep
          simp only [BtSt.reserved, btReset] at c ⊢
          refine ⟨?_, r, t, hm, ?_, ?_⟩ <;>
            (try simp only [RunEnd.state, BtSt.reserved]) <;> omega
        · rename_i st' hout
          rw [hout] at hstep
          simp only [AttemptOut.state] at hstep
          split
          · obtain ⟨c, r, t, hm, p, d⟩ := hstep
            simp only [BtSt.reserved, btReset] at c ⊢
            refine ⟨?_, r, t, hm, ?_, ?_⟩ <;>
              (try simp only [RunEnd.state, BtSt.reserved]) <;> omega
          · refine Within.mono
              (Within.trans (a := btReset re + (work + regSize * trail)) ?_
                (ih _ st' hstep.btRoom hstep.trailRoom hstep.held)) (by omega)
            obtain ⟨c, r, t, hm, p, d⟩ := hstep
            simp only [BtSt.reserved, btReset] at c ⊢
            refine ⟨?_, r, t, hm, ?_, ?_⟩ <;>
              (try simp only [BtSt.reserved]) <;> omega

/-- `bt_run` on the plain path, with the bindings taken out: the two
guards, the loop over the starting positions, and the delivery a match
pays for. -/
theorem btRun_zero (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) :
    btRun re s start mo lim 0 0 =
      if start > s.size then ⟨.badInput, #[], {}⟩
      else if btSetup re > lim.mem || btSetup re > lim.cost then
        ⟨.resourceExceeded, #[], {}⟩
      else
        match btLoop re s mo lim start (s.size + 1 - start) start
            ⟨Array.replicate re.nregs unset32, #[], 0, #[], 0,
              ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ with
        | .matched st =>
            if btDeliver re > lim.cost - st.m.cost then
              ⟨.resourceExceeded, #[], st.usage⟩
            else
              ⟨.matched, st.regs.extract 0 re.novec,
                ⟨st.m.cost + btDeliver re, st.stackpeak, st.m.peak⟩⟩
        | .noMatch st => ⟨.noMatch, #[], st.usage⟩
        | .exceeded st => ⟨.resourceExceeded, #[], st.usage⟩ := rfl

/-- R-6 through R-8 for one call, against the section 5 numbers: a run
whose attempts stay inside the root region's prices charges at most the
setup, one delivery, one reset and one attempt per starting position, and
three times the scratch it ends up reserving; it never pushes deeper than
the claim; and it holds at most the setup plus twice that scratch. -/
theorem btRun_within {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start stack trail work : Nat}
    (hatt : AttemptsWithin re s mo lim start (btSetup re) stack trail work) :
    (btRun re s start mo lim 0 0).usage.cost ≤
        btSetup re + btDeliver re
          + ((s.size + 1) * (btReset re + (work + regSize * trail))
            + 3 * btScratch stack trail) ∧
      (btRun re s start mo lim 0 0).usage.stack ≤ stack ∧
      (btRun re s start mo lim 0 0).usage.mem ≤
        btSetup re + 2 * btScratch stack trail := by
  rw [btRun_zero]
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  have hloop := btLoop_within hatt (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], 0, #[], 0,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ (Nat.zero_le _) (Nat.zero_le _)
    (by simp [BtSt.reserved])
  have hsteps : (s.size + 1 - start) * (btReset re + (work + regSize * trail)) ≤
      (s.size + 1) * (btReset re + (work + regSize * trail)) :=
    Nat.mul_le_mul_right _ (by omega)
  split
  · rename_i st' hout
    rw [hout] at hloop
    simp only [RunEnd.state] at hloop
    obtain ⟨c, r, t, hm, p, d⟩ := hloop
    simp only [BtSt.reserved, btScratch, btSize, undoSize] at c r t p d ⊢
    refine ⟨?_, ?_, ?_⟩ <;> split <;>
      simp only [BtSt.usage] <;> omega
  · rename_i st' hout
    rw [hout] at hloop
    simp only [RunEnd.state] at hloop
    obtain ⟨c, r, t, hm, p, d⟩ := hloop
    simp only [BtSt.reserved, btScratch, btSize, undoSize] at c r t p d ⊢
    exact ⟨by simp only [BtSt.usage]; omega, by simp only [BtSt.usage]; omega,
      by simp only [BtSt.usage]; omega⟩
  · rename_i st' hout
    rw [hout] at hloop
    simp only [RunEnd.state] at hloop
    obtain ⟨c, r, t, hm, p, d⟩ := hloop
    simp only [BtSt.reserved, btScratch, btSize, undoSize] at c r t p d ⊢
    exact ⟨by simp only [BtSt.usage]; omega, by simp only [BtSt.usage]; omega,
      by simp only [BtSt.usage]; omega⟩

/-! ## The growth schedule, as the VM runs it -/

/-- `charge_grow` with its bindings taken out, so the decisions can be read
one at a time. -/
theorem chargeGrow_unfold (oldcap len esize maxv : Nat) (m : Meter)
    (lim : Limits) :
    chargeGrow oldcap len esize maxv m lim =
      if len < oldcap then some (m, oldcap)
      else if len ≥ maxv then none
      else if min maxv (max growMin (oldcap * growFactor)) * esize >
          lim.mem - m.mem then none
      else if min maxv (max growMin (oldcap * growFactor)) * esize +
          oldcap * esize > lim.cost - m.cost then none
      else
        some ({ cost := m.cost +
                  (min maxv (max growMin (oldcap * growFactor)) * esize +
                    oldcap * esize)
                mem := m.mem +
                  min maxv (max growMin (oldcap * growFactor)) * esize -
                  oldcap * esize
                peak := max m.peak
                  (m.mem + min maxv (max growMin (oldcap * growFactor)) * esize) },
          min maxv (max growMin (oldcap * growFactor))) := rfl

/-- What one `charge_grow` did: nothing, because the array still had room,
or one step of the schedule — the new capacity, both buffers charged as
cost, the old one given back as memory, and the peak taken while both are
held. -/
theorem chargeGrow_cases {oldcap len esize maxv cap : Nat} {m m' : Meter}
    {lim : Limits}
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    (len < oldcap ∧ m' = m ∧ cap = oldcap) ∨
      (oldcap ≤ len ∧ len < maxv ∧
        cap = min maxv (max growMin (oldcap * growFactor)) ∧
        m'.cost = m.cost + (cap * esize + oldcap * esize) ∧
        m'.mem = m.mem + cap * esize - oldcap * esize ∧
        m'.peak = max m.peak (m.mem + cap * esize) ∧
        cap * esize ≤ lim.mem - m.mem) := by
  rw [chargeGrow_unfold] at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨hlt, h.1.symm, h.2.symm⟩
  · rename_i hlt
    split at h
    · exact absurd h (by simp)
    · rename_i hmax
      split at h
      · exact absurd h (by simp)
      · rename_i hmem
        split at h
        · exact absurd h (by simp)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hm, hc⟩ := h
          subst hm
          subst hc
          refine Or.inr ⟨by omega, by omega, rfl, rfl, rfl, rfl, by omega⟩

/-- The declared maximum never clamps a growth a caller's memory limit
admits. Reaching it would mean holding the whole allocation ceiling in one
array, and the limit that paid for the new buffer had to cover the old one
beside it — so the schedule really does double, which is what the section 5
capacity of `4 + 2x` counts on. -/
theorem chargeGrow_doubles {oldcap len esize maxv cap other base : Nat}
    {m m' : Meter} {lim : Limits}
    (hes : 0 < esize) (hgm : growMin ≤ maxv)
    (hceil : ceiling < maxv * esize + esize) (hlim : lim.mem ≤ ceiling)
    (hmem : m.mem = base + oldcap * esize + other)
    (hlen : oldcap ≤ len)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    cap = max growMin (oldcap * growFactor) := by
  rcases chargeGrow_cases h with ⟨hlt, -, -⟩ | ⟨-, hmax, hcap, -, -, -, hroom⟩
  · omega
  · rcases Nat.le_total (max growMin (oldcap * growFactor)) maxv with hle | hle
    · omega
    · -- the schedule asked for more than the declared maximum, so the
      -- maximum is what was reserved, and the limit had to cover it beside
      -- the buffer being copied out of
      have hcapv : cap = maxv := by omega
      subst hcapv
      have hpos : 0 < cap * esize := Nat.mul_pos (by omega) hes
      have hzero : oldcap = 0 := by
        rcases Nat.eq_zero_or_pos oldcap with hz | hz
        · exact hz
        · have h1 : esize ≤ oldcap * esize := Nat.le_mul_of_pos_left _ hz
          omega
      subst hzero
      omega

/-- One step of the schedule, weighed: the new capacity is inside the
section 5 capacity of the claim, the cost it charges is covered by three
times the reservation it leaves standing, the memory identity survives, and
the peak taken while both buffers are held is at most twice the new
reservation. -/
theorem chargeGrow_within {oldcap len esize maxv cap other base claim : Nat}
    {m m' : Meter} {lim : Limits}
    (hes : 0 < esize) (hgm : growMin ≤ maxv)
    (hceil : ceiling < maxv * esize + esize) (hlim : lim.mem ≤ ceiling)
    (hmem : m.mem = base + oldcap * esize + other)
    (hlen : len < claim) (hroom : oldcap ≤ capacityOf claim)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap)) :
    cap ≤ capacityOf claim ∧ oldcap ≤ cap ∧
      m'.cost + 3 * (oldcap * esize) ≤ m.cost + 3 * (cap * esize) ∧
      m'.mem = base + cap * esize + other ∧
      m'.peak ≤ max m.peak (base + 2 * (cap * esize) + other) := by
  rcases chargeGrow_cases h with ⟨hlt, hm, hc⟩ | ⟨hge, -, -, hcost, hmem', hpeak, -⟩
  · subst hm
    subst hc
    exact ⟨hroom, Nat.le_refl _, by omega, hmem, by omega⟩
  · have hdouble := chargeGrow_doubles hes hgm hceil hlim hmem hge h
    have hgrown : growFactor * (oldcap * esize) ≤ cap * esize := by
      have hstep : growFactor * oldcap ≤ cap := by
        simp only [growMin, growFactor] at hdouble ⊢
        omega
      have := Nat.mul_le_mul_right esize hstep
      rwa [Nat.mul_assoc] at this
    have hclaim : cap ≤ capacityOf claim := by
      unfold capacityOf
      rw [if_neg (by omega)]
      simp only [growMin, growFactor] at hdouble ⊢
      omega
    have hold : oldcap * esize ≤ cap * esize := by
      simp only [growFactor] at hgrown
      omega
    simp only [growFactor] at hgrown
    exact ⟨hclaim, Nat.le_of_mul_le_mul_right (by omega) hes, by omega, by omega,
      by omega⟩

/-- The backtrack stack's entry size and declared maximum meet what the
growth lemmas ask for. -/
theorem btSize_schedule :
    0 < btSize ∧ growMin ≤ maxStack ∧ ceiling < maxStack * btSize + btSize := by
  decide

/-- And the undo trail's. -/
theorem undoSize_schedule :
    0 < undoSize ∧ growMin ≤ maxTrail ∧
      ceiling < maxTrail * undoSize + undoSize := by
  decide

/-- A push that stays inside the claimed depth stays inside the claimed
scratch: the entry is charged against the reservation it grows, and nothing
else moves. -/
theorem pushBt_within {st st' : BtSt} {lim : Limits}
    {pc pos mark setup stack trail : Nat}
    (hlim : lim.mem ≤ ceiling) (hmem : st.m.mem = setup + st.reserved)
    (hbt : st.btCap ≤ capacityOf stack) (htr : st.trailCap ≤ capacityOf trail)
    (hsize : st.bt.size < stack)
    (h : pushBt st lim pc pos mark = some st') :
    Within setup stack trail 0 st st' ∧ st'.bt.size = st.bt.size + 1 ∧
      st'.trail = st.trail ∧ st'.trailCap = st.trailCap ∧
      st'.stackpeak = st.stackpeak := by
  simp only [pushBt] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i pair mm cap hg
      simp only [Option.some.injEq] at h
      obtain ⟨hes, hgm, hceil⟩ := btSize_schedule
      obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
        chargeGrow_within (claim := stack) (base := setup)
          (other := st.trailCap * undoSize) hes hgm hceil hlim
          (by simp only [BtSt.reserved] at hmem; omega) hsize hbt hg
      have hw : cap * btSize ≤ capacityOf stack * btSize :=
        Nat.mul_le_mul_right _ hcap
      have hu : st.trailCap * undoSize ≤ capacityOf trail * undoSize :=
        Nat.mul_le_mul_right _ htr
      subst h
      simp only [BtSt.reserved] at hmem
      refine ⟨⟨?_, hcap, htr, ?_, ?_, ?_⟩, by simp, rfl, rfl, rfl⟩ <;>
        simp only [BtSt.reserved, btScratch] <;> omega

/-- The same for a fork, whose stack peak is the push it just made. -/
theorem fork_within {st st' : BtSt} {lim : Limits}
    {target pos setup stack trail : Nat}
    (hlim : lim.mem ≤ ceiling) (hmem : st.m.mem = setup + st.reserved)
    (hbt : st.btCap ≤ capacityOf stack) (htr : st.trailCap ≤ capacityOf trail)
    (hsize : st.bt.size < stack)
    (h : fork st lim target pos = some st') :
    Within setup stack trail 0 st st' ∧ st'.bt.size = st.bt.size + 1 ∧
      st'.trail = st.trail ∧ st'.trailCap = st.trailCap := by
  simp only [fork] at h
  split at h
  · exact absurd h (by simp)
  · rename_i mid hp
    obtain ⟨⟨c, r, t, hm, p, d⟩, hbtsize, htrail, htrcap, hpeak⟩ :=
      pushBt_within hlim hmem hbt htr hsize hp
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨⟨?_, r, t, ?_, ?_, ?_⟩, hbtsize, htrail, htrcap⟩ <;>
      (dsimp only [BtSt.reserved] at c hm ⊢; omega)

/-- An undo entry recorded inside the claimed trail length, priced the same
way. The path that records nothing — there is nothing to backtrack to —
charges nothing at all. -/
theorem writeReg_within {st st' : BtSt} {lim : Limits} {slot : Nat}
    {value : UInt32} {setup stack trail : Nat}
    (hlim : lim.mem ≤ ceiling) (hmem : st.m.mem = setup + st.reserved)
    (hbt : st.btCap ≤ capacityOf stack) (htr : st.trailCap ≤ capacityOf trail)
    (hsize : st.trail.size < trail)
    (h : writeReg st lim slot value = some st') :
    Within setup stack trail 0 st st' ∧ st'.trail.size ≤ st.trail.size + 1 ∧
      st'.bt = st.bt ∧ st'.btCap = st.btCap ∧ st'.stackpeak = st.stackpeak := by
  simp only [writeReg] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i pair mm cap hg
      simp only [Option.some.injEq] at h
      obtain ⟨hes, hgm, hceil⟩ := undoSize_schedule
      obtain ⟨hcap, hold, hcost, hmem', hpeak⟩ :=
        chargeGrow_within (claim := trail) (base := setup)
          (other := st.btCap * btSize) hes hgm hceil hlim
          (by simp only [BtSt.reserved] at hmem; omega) hsize htr hg
      have hw : cap * undoSize ≤ capacityOf trail * undoSize :=
        Nat.mul_le_mul_right _ hcap
      have hu : st.btCap * btSize ≤ capacityOf stack * btSize :=
        Nat.mul_le_mul_right _ hbt
      subst h
      simp only [BtSt.reserved] at hmem
      refine ⟨⟨?_, hbt, hcap, ?_, ?_, ?_⟩, by simp, rfl, rfl, rfl⟩ <;>
        simp only [BtSt.reserved, btScratch] <;> omega
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨⟨?_, hbt, htr, ?_, ?_, ?_⟩, by simp, rfl, rfl, rfl⟩ <;>
      (dsimp only [BtSt.reserved] at hmem ⊢; omega)

/-! ## R-6, R-7 and R-8 for the backtracking configuration -/

/-- What an accepted certificate promises about a call, in the numbers
BOUNDS.md section 5 writes down. -/
theorem certCheck_bt_dom {re : Re} {cert : Cert}
    (h : certCheck re .backtrack cert = .crOk) (n : Nat) :
    btSetup re + btDeliver re
        + ((n + 1) * (btReset re
            + ((cert.prices[0]!).work.val n + regSize * cert.trail.val n))
          + 3 * btScratch (cert.stack.val n) (cert.trail.val n)) ≤ cert.cost.val n ∧
      btSetup re + btDeliver re
        + 2 * btScratch (cert.stack.val n) (cert.trail.val n) ≤ cert.mem.val n := by
  obtain ⟨hs, ht, ⟨over, hcharge⟩, -, -⟩ := certCheck_bt_spec h
  obtain ⟨hcost, hmem, hstack, htrail⟩ := chargeCall_dom hs ht hcharge n
  rw [hstack, htrail]
  exact ⟨hcost, hmem⟩

/-- R-6, the backtracking half: a run of a program whose certificate the
checker accepted charges no more cost than the certificate names at the
subject length. -/
theorem btRun_cost_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hatt : AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size)) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size := by
  obtain ⟨hrun, -, -⟩ := btRun_within hatt
  obtain ⟨hdom, -⟩ := certCheck_bt_dom hcert s.size
  omega

/-- R-7: nor does it push more backtrack entries. -/
theorem btRun_stack_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert}
    (hatt : AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size)) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  (btRun_within hatt).2.1

/-- R-8: nor does it reserve more scratch. The peak counts the growth
overlap, which is where the factor of two in the section 5 memory line
comes from. -/
theorem btRun_mem_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hatt : AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size)) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size := by
  obtain ⟨-, -, hrun⟩ := btRun_within hatt
  obtain ⟨-, hdom⟩ := certCheck_bt_dom hcert s.size
  omega


/-! ## The straight-line composition (BOUNDS.md section 4.1, no children) -/

/-- The opcodes a region may hold loose: everything that does not fork, jump
or drive a repetition. It is the set both of the checker's walks admit, and
the first five rows of the BOUNDS.md section 3 table. -/
def Op.loose : Op → Bool
  | .split | .jump | .repZero | .repLoop | .repEnter | .repNext => false
  | _ => true

/-- What one entry into a straight-line stretch visits: one instruction at a
time, up to and including the Accept that ends the attempt. -/
def visitCount (code : Array Inst) (hi pc : Nat) : Nat :=
  if pc < hi then
    if (code[pc]!).op = .accept then 1 else 1 + visitCount code hi (pc + 1)
  else 0
termination_by hi - pc
decreasing_by omega

/-- The visit count, one instruction at a time. -/
theorem visitCount_succ (code : Array Inst) (hi pc : Nat) (h : pc < hi) :
    visitCount code hi pc =
      if (code[pc]!).op = .accept then 1
      else 1 + visitCount code hi (pc + 1) := by
  rw [visitCount, if_pos h]

/-- Past the end of the range there is nothing left to visit. -/
theorem visitCount_done (code : Array Inst) (hi pc : Nat) (h : ¬ pc < hi) :
    visitCount code hi pc = 0 := by
  rw [visitCount, if_neg h]

/-- A stretch that meets no Accept splits: the visits up to a point plus the
visits from it. -/
theorem visitCount_split {code : Array Inst} {mid hi : Nat} :
    ∀ (k lo : Nat), mid - lo ≤ k → lo ≤ mid → mid ≤ hi →
      (∀ q, lo ≤ q → q < mid → (code[q]!).op ≠ .accept) →
      visitCount code hi lo = visitCount code mid lo + visitCount code hi mid := by
  intro k
  induction k with
  | zero =>
      intro lo hk hlo hmid hno
      have hle : lo = mid := by omega
      subst hle
      rw [visitCount_done code lo lo (by omega)]
      omega
  | succ k ih =>
      intro lo hk hlo hmid hno
      rcases Nat.eq_or_lt_of_le hlo with rfl | hlt
      · rw [visitCount_done code lo lo (by omega)]
        omega
      · rw [visitCount_succ code hi lo (by omega),
          visitCount_succ code mid lo hlt]
        simp only [if_neg (hno lo (Nat.le_refl _) hlt)]
        rw [ih (lo + 1) (by omega) (by omega) hmid
          (fun q h1 h2 => hno q (by omega) h2)]
        omega

/-- And one that meets an Accept stops there, whatever comes after. -/
theorem visitCount_stop {code : Array Inst} {mid hi : Nat} :
    ∀ (k lo : Nat), mid - lo ≤ k → mid ≤ hi →
      (∃ q, lo ≤ q ∧ q < mid ∧ (code[q]!).op = .accept) →
      visitCount code hi lo = visitCount code mid lo := by
  intro k
  induction k with
  | zero =>
      intro lo hk hmid hacc
      obtain ⟨q, h1, h2, -⟩ := hacc
      omega
  | succ k ih =>
      intro lo hk hmid hacc
      obtain ⟨q, h1, h2, hq⟩ := hacc
      rw [visitCount_succ code hi lo (by omega),
        visitCount_succ code mid lo (by omega)]
      by_cases hlo : (code[lo]!).op = .accept
      · rw [if_pos hlo, if_pos hlo]
      · have hne : lo ≠ q := fun hqe => hlo (hqe ▸ hq)
        rw [if_neg hlo, if_neg hlo,
          ih (lo + 1) (by omega) hmid ⟨q, by omega, h2, hq⟩]

set_option maxHeartbeats 1000000 in
/-- The checker's own walk over a stretch with no children, read as two
facts: every instruction in it is one a region may hold loose — the walk
refuses the others by name — and the work it accumulated covers one visit
per instruction up to the first Accept, at the flow arriving. -/
theorem scanSpanGo_straight {code : Array Inst} {regions : Array Region}
    {prices : Array Price} {sibs : Array Nat} {hi n : Nat} :
    ∀ (k pc : Nat), hi - pc ≤ k → ∀ (acc acc' : Acc) (over over' : Bool),
      scanSpanGo code regions prices sibs hi pc none32 acc over =
        (.crOk, acc', over') → over' = false →
      (∀ q, pc ≤ q → q < hi → (code[q]!).op.loose = true) ∧ over = false ∧
        acc.work.val n + visitCount code hi pc * acc.flow.val n ≤
          acc'.work.val n ∧
        ((∀ q, pc ≤ q → q < hi → (code[q]!).op ≠ .accept) →
          acc'.flow = acc.flow) := by
  intro k
  induction k with
  | zero =>
      intro pc hk acc acc' over over' h hover
      rw [scanSpanGo, dif_neg (by omega)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, hacc, hov⟩ := h
      subst hacc
      subst hov
      refine ⟨fun q h1 h2 => by omega, hover, ?_, fun _ => rfl⟩
      rw [visitCount, if_neg (by omega)]
      omega
  | succ k ih =>
      intro pc hk acc acc' over over' h hover
      by_cases hpc : pc < hi
      · rw [scanSpanGo, dif_pos hpc] at h
        rw [if_neg (by simp)] at h
        dsimp only at h
        split at h
        all_goals rename_i hop
        all_goals
          first
            | (simp only [Prod.mk.injEq] at h
               exact absurd h.1 (by decide))
            | (obtain ⟨hloose, hov, hwork, hflow⟩ :=
                 ih (pc + 1) (by omega) _ _ _ _ h hover
               have hov0 : over = false := by
                 first
                   | exact polyAdd_snd hov
                   | exact polyAdd_snd (polyAdd_snd hov)
               have hvis : acc.work.val n + acc.flow.val n ≤
                   (polyAdd acc.work acc.flow over).1.val n := by
                 first
                   | exact polyAdd_le hov n
                   | exact polyAdd_le (polyAdd_snd hov) n
               dsimp only at hwork hflow
               refine ⟨?_, hov0, ?_, ?_⟩
               · intro q h1 h2
                 rcases Nat.eq_or_lt_of_le h1 with rfl | h3
                 · rw [hop]
                   rfl
                 · exact hloose q (by omega) h2
               · rw [visitCount, if_pos hpc]
                 first
                   | (rw [if_pos (by rw [hop])]
                      rw [Poly.val_zero] at hwork
                      omega)
                   | (rw [if_neg (by rw [hop]; decide)]
                      have hexp : (1 + visitCount code hi (pc + 1)) *
                          acc.flow.val n = acc.flow.val n +
                            visitCount code hi (pc + 1) * acc.flow.val n := by
                        rw [Nat.add_mul, Nat.one_mul]
                      omega)
               · intro hno
                 first
                   | exact absurd hop (hno pc (Nat.le_refl _) hpc)
                   | exact hflow (fun q h1 h2 => hno q (by omega) h2))
      · rw [scanSpanGo, dif_neg hpc] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, hacc, hov⟩ := h
        subst hacc
        subst hov
        refine ⟨fun q h1 h2 => by omega, hover, ?_, fun _ => rfl⟩
        rw [visitCount, if_neg hpc]
        omega

set_option maxHeartbeats 1000000 in
/-- The same walk one level up: a straight-line range that has children in
it. At a child the walk charges the flow times what the child claims and
jumps to the child's end, so what the child's own claim is worth is all the
parent needs to know — which is BOUNDS.md section 4's "soundness is an
induction one step deep", made literal.

`hkid` is that one step: for every region the walk can meet, its claim
covers the visits inside it, the instructions inside it are ones a region
may hold loose, its `outs` is at least one unless it swallows the attempt
with an Accept, and its range ends inside this one. -/
theorem scanSpanGo_children {code : Array Inst} {regions : Array Region}
    {prices : Array Price} {sibs : Array Nat} {hi n : Nat}
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      (regions[c]!).lo < (regions[c]!).hi →
      visitCount code (regions[c]!).hi (regions[c]!).lo ≤
          (prices[c]!).work.val n ∧
        (∀ q, (regions[c]!).lo ≤ q → q < (regions[c]!).hi →
          (code[q]!).op.loose = true) ∧
        ((∀ q, (regions[c]!).lo ≤ q → q < (regions[c]!).hi →
          (code[q]!).op ≠ .accept) → 1 ≤ (prices[c]!).outs.val n) ∧
        (regions[c]!).hi ≤ hi) :
    ∀ (k pc cursor : Nat), P cursor → hi - pc ≤ k →
      ∀ (acc acc' : Acc) (over over' : Bool),
      scanSpanGo code regions prices sibs hi pc cursor acc over =
        (.crOk, acc', over') → over' = false →
      (∀ q, pc ≤ q → q < hi → (code[q]!).op.loose = true) ∧ over = false ∧
        acc.work.val n + visitCount code hi pc * acc.flow.val n ≤
          acc'.work.val n := by
  intro k
  induction k with
  | zero =>
      intro pc cursor hP hk acc acc' over over' h hover
      rw [scanSpanGo, dif_neg (by omega)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, hacc, hov⟩ := h
      subst hacc
      subst hov
      refine ⟨fun q h1 h2 => by omega, hover, ?_⟩
      rw [visitCount_done code hi pc (by omega)]
      omega
  | succ k ih =>
      intro pc cursor hP hk acc acc' over over' h hover
      by_cases hpc : pc < hi
      · rw [scanSpanGo, dif_pos hpc] at h
        split at h
        · -- a child starts here
          rename_i hcond
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
          split at h
          · exact absurd h (by simp)
          rename_i hkhi
          dsimp only at h
          obtain ⟨hcw, hcloose, hcouts, hchi⟩ :=
            hkid cursor hP hcond.1 (by omega)
          obtain ⟨hloose, hov, hwork⟩ :=
            ih (regions[cursor]!).hi (sibs[cursor]!) (hsib cursor hP hcond.1)
              (by omega) _ _ _ _ h hover
          dsimp only at hwork
          have f6 := polyMul_snd hov
          have f5 := polyAdd_snd f6
          have f4 := polyMul_snd f5
          have f3 := polyAdd_snd f4
          have f2 := polyMul_snd f3
          have f1 := polyAdd_snd f2
          have vcw := polyMul_eq f1 n
          have vw := polyAdd_le f2 n
          have von := polyMul_eq hov n
          rw [von] at hwork
          refine ⟨?_, polyMul_snd f1, ?_⟩
          · intro q h1 h2
            by_cases hin : q < (regions[cursor]!).hi
            · exact hcloose q (by omega) hin
            · exact hloose q (by omega) h2
          · by_cases hacc : ∃ q, (regions[cursor]!).lo ≤ q ∧
                q < (regions[cursor]!).hi ∧ (code[q]!).op = .accept
            · rw [visitCount_stop (mid := (regions[cursor]!).hi) hi pc
                (by omega) hchi (by rw [hcond.2] at hacc; exact hacc)]
              have hm : visitCount code (regions[cursor]!).hi pc *
                  acc.flow.val n ≤
                    acc.flow.val n * (prices[cursor]!).work.val n := by
                rw [Nat.mul_comm]
                refine Nat.mul_le_mul_left _ ?_
                rw [← hcond.2]
                exact hcw
              omega
            · have hno : ∀ q, (regions[cursor]!).lo ≤ q →
                  q < (regions[cursor]!).hi → (code[q]!).op ≠ .accept := by
                intro q h1 h2 hq
                exact hacc ⟨q, h1, h2, hq⟩
              have houts := hcouts hno
              rw [visitCount_split (mid := (regions[cursor]!).hi) hi pc
                (by omega) (by omega) hchi
                (fun q h1 h2 => hno q (by rw [hcond.2]; omega) h2), Nat.add_mul]
              have hm : visitCount code (regions[cursor]!).hi pc *
                  acc.flow.val n ≤
                    acc.flow.val n * (prices[cursor]!).work.val n := by
                rw [Nat.mul_comm]
                refine Nat.mul_le_mul_left _ ?_
                rw [← hcond.2]
                exact hcw
              have hm2 : visitCount code hi (regions[cursor]!).hi *
                  acc.flow.val n ≤ visitCount code hi (regions[cursor]!).hi *
                    (acc.flow.val n * (prices[cursor]!).outs.val n) :=
                Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
              omega
        · -- an instruction this range holds itself
          rename_i hcond
          dsimp only at h
          split at h
          all_goals rename_i hop
          all_goals
            first
              | (simp only [Prod.mk.injEq] at h
                 exact absurd h.1 (by decide))
              | (obtain ⟨hloose, hov, hwork⟩ :=
                   ih (pc + 1) _ hP (by omega) _ _ _ _ h hover
                 have hov0 : over = false := by
                   first
                     | exact polyAdd_snd hov
                     | exact polyAdd_snd (polyAdd_snd hov)
                 have hvis : acc.work.val n + acc.flow.val n ≤
                     (polyAdd acc.work acc.flow over).1.val n := by
                   first
                     | exact polyAdd_le hov n
                     | exact polyAdd_le (polyAdd_snd hov) n
                 dsimp only at hwork
                 refine ⟨?_, hov0, ?_⟩
                 · intro q h1 h2
                   rcases Nat.eq_or_lt_of_le h1 with rfl | h3
                   · rw [hop]
                     rfl
                   · exact hloose q (by omega) h2
                 · rw [visitCount_succ code hi pc hpc]
                   first
                     | (rw [if_pos (by rw [hop])]
                        rw [Poly.val_zero] at hwork
                        omega)
                     | (rw [if_neg (by rw [hop]; decide)]
                        have hexp : (1 + visitCount code hi (pc + 1)) *
                            acc.flow.val n = acc.flow.val n +
                              visitCount code hi (pc + 1) * acc.flow.val n := by
                          rw [Nat.add_mul, Nat.one_mul]
                        omega))
      · rw [scanSpanGo, dif_neg hpc] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, hacc, hov⟩ := h
        subst hacc
        subst hov
        refine ⟨fun q h1 h2 => by omega, hover, ?_⟩
        rw [visitCount_done code hi pc hpc]
        omega

/-- A register write with nothing to backtrack to records no undo entry and
charges nothing: `write_reg` asks about the backtrack stack first. -/
theorem writeReg_empty {st : BtSt} {lim : Limits} {slot : Nat} {value : UInt32}
    (h : st.bt.size = 0) :
    writeReg st lim slot value =
      some { st with regs := st.regs.set! slot value } := by
  simp only [writeReg]
  rw [if_neg (by omega)]

/-- A failed path with nothing to backtrack to ends the attempt, and the
trail it lets go of was empty anyway. -/
theorem btFail_empty {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel : Nat} {st : BtSt} (h : st.bt.size = 0) :
    btFail re s mo lim start attempt fuel st =
      .exhausted { st with trail := #[] } := by
  rw [btFail, dif_pos h]

/-- What one visit of an instruction a region holds loose can do: charge its
unit and walk on, charge it and hand the failure to a stack that has nothing
on it, or charge it and answer a match. No arm of it forks, jumps, or
touches the trail, which is what makes the straight-line count exact. -/
theorem btStep_loose {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hloose : (re.code[pc]!).op.loose = true) (hlim : ¬ st.m.cost ≥ lim.cost)
    (hempty : st.bt.size = 0) :
    (∃ pos' regs, btStep re s mo lim start attempt (fuel + 1) pc pos st =
        btStep re s mo lim start attempt fuel (pc + 1) pos'
          { st with m := { st.m with cost := st.m.cost + 1 }, regs := regs }) ∨
      (btStep re s mo lim start attempt (fuel + 1) pc pos st =
        btFail re s mo lim start attempt fuel
          { st with m := { st.m with cost := st.m.cost + 1 } }) ∨
      (∃ regs, btStep re s mo lim start attempt (fuel + 1) pc pos st =
        .found pos
          { st with m := { st.m with cost := st.m.cost + 1 }, regs := regs }) := by
  simp only [btStep]
  rw [if_neg hlim]
  repeat' split
  all_goals
    first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr ⟨_, rfl⟩)
      | exact absurd hloose (by rw [‹re.code[pc]!.op = Op.split›]; decide)
      | exact absurd hloose (by rw [‹re.code[pc]!.op = Op.jump›]; decide)
      | exact absurd hloose (by rw [‹re.code[pc]!.op = Op.repZero›]; decide)
      | exact absurd hloose (by rw [‹re.code[pc]!.op = Op.repLoop›]; decide)
      | exact absurd hloose (by rw [‹re.code[pc]!.op = Op.repEnter›]; decide)
      | exact absurd hloose (by rw [‹re.code[pc]!.op = Op.repNext›]; decide)
      | (rename_i hnone
         simp [writeReg, hempty] at hnone)
  rename_i hsome
  subst hsome
  exact Or.inl ⟨_, _, rfl⟩

/-- The Accept arm, read on its own: an attempt that reaches it either
answers a match or hands one last failure to the stack. -/
theorem btStep_accept {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hacc : (re.code[pc]!).op = .accept) (hlim : ¬ st.m.cost ≥ lim.cost) :
    (∃ regs, btStep re s mo lim start attempt (fuel + 1) pc pos st =
        .found pos
          { st with m := { st.m with cost := st.m.cost + 1 }, regs := regs }) ∨
      (btStep re s mo lim start attempt (fuel + 1) pc pos st =
        btFail re s mo lim start attempt fuel
          { st with m := { st.m with cost := st.m.cost + 1 } }) := by
  simp only [btStep]
  rw [if_neg hlim]
  simp only [hacc]
  split
  · exact Or.inr rfl
  · exact Or.inl ⟨_, rfl⟩

/-- What a straight-line stretch does to a run: it charges its visits and
moves nothing else. Nothing forks, so nothing is ever pushed; nothing is
recorded, because `write_reg` only records while there is somewhere to
backtrack to; and neither array grows. -/
structure Quiet (c : Nat) (st out : BtSt) : Prop where
  cost : out.m.cost ≤ st.m.cost + c
  empty : out.bt.size = 0
  btCap : out.btCap = st.btCap
  trailCap : out.trailCap = st.trailCap
  mem : out.m.mem = st.m.mem
  peak : out.m.peak = st.m.peak
  deepest : out.stackpeak = st.stackpeak

theorem Quiet.still {c : Nat} {st : BtSt} (h : st.bt.size = 0) : Quiet c st st :=
  ⟨by omega, h, rfl, rfl, rfl, rfl, rfl⟩

theorem Quiet.mono {a b : Nat} {st out : BtSt} (h : Quiet a st out) (hle : a ≤ b) :
    Quiet b st out :=
  ⟨by have := h.cost; omega, h.empty, h.btCap, h.trailCap, h.mem, h.peak,
    h.deepest⟩

/-- The state one visit leaves behind: the unit charged, and whatever
register the visit wrote. -/
def BtSt.visited (st : BtSt) (regs : Array UInt32) : BtSt :=
  { st with m := { st.m with cost := st.m.cost + 1 }, regs := regs }

/-- One visit charged, then a stretch. A register write moves nothing the
accounting follows, which is why the register file is all that changes. -/
theorem Quiet.step {c : Nat} {st out : BtSt} {regs : Array UInt32}
    (h : Quiet c (st.visited regs) out) : Quiet (1 + c) st out := by
  obtain ⟨hc, he, hb, ht, hm, hp, hd⟩ := h
  simp only [BtSt.visited] at hc hb ht hm hp hd
  exact ⟨by omega, he, hb, ht, hm, hp, hd⟩

/-- The failure that ends an attempt: the stack is empty, so there is
nowhere to go and nothing to replay. -/
theorem btFail_charged {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel : Nat} {st : BtSt} (h : st.bt.size = 0) (c : Nat)
    (hc : 1 ≤ c) :
    Quiet c st (btFail re s mo lim start attempt fuel
      (st.visited st.regs)).state := by
  rw [btFail_empty (show (st.visited st.regs).bt.size = 0 from h)]
  exact ⟨show st.m.cost + 1 ≤ st.m.cost + c by omega, h, rfl, rfl, rfl, rfl, rfl⟩

/-- And the match that ends it the other way. -/
theorem found_quiet {st : BtSt} {regs : Array UInt32} {pos c : Nat}
    (h : st.bt.size = 0) (hc : 1 ≤ c) :
    Quiet c st (AttemptOut.found pos (st.visited regs)).state :=
  ⟨show st.m.cost + 1 ≤ st.m.cost + c by omega, h, rfl, rfl, rfl, rfl, rfl⟩

/-- One attempt over a straight-line program: it charges one unit per
instruction up to the Accept that ends it, and moves nothing else. This is
BOUNDS.md section 4.1 against the VM, for a region with no children. -/
theorem btStep_quiet {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt : Nat}
    (hloose : ∀ q, q < re.code.size → (re.code[q]!).op.loose = true) :
    ∀ (fuel pc pos : Nat) (st : BtSt), st.bt.size = 0 →
      (∃ a, pc ≤ a ∧ a < re.code.size ∧ (re.code[a]!).op = .accept) →
      Quiet (visitCount re.code re.code.size pc) st
        (btStep re s mo lim start attempt fuel pc pos st).state := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc pos st hempty _
      rw [btStep]
      exact Quiet.still hempty
  | succ fuel ih =>
      intro pc pos st hempty hreach
      obtain ⟨a, hpa, hah, hacode⟩ := hreach
      have hpc : pc < re.code.size := by omega
      have hvis1 : 1 ≤ visitCount re.code re.code.size pc := by
        rw [visitCount, if_pos hpc]
        split <;> omega
      by_cases hlim : st.m.cost ≥ lim.cost
      · rw [btStep_exceeded_of_le hlim]
        exact Quiet.still hempty
      · by_cases hisacc : (re.code[pc]!).op = .accept
        · rcases btStep_accept hisacc hlim with ⟨regs, heq⟩ | heq
          · rw [heq]
            exact found_quiet hempty hvis1
          · rw [heq]
            exact btFail_charged hempty _ hvis1
        · have hstep : visitCount re.code re.code.size pc =
              1 + visitCount re.code re.code.size (pc + 1) := by
            rw [visitCount, if_pos hpc, if_neg hisacc]
          rcases btStep_loose (hloose pc hpc) hlim hempty with
            ⟨pos', regs, heq⟩ | heq | ⟨regs, heq⟩
          · rw [heq, hstep]
            refine Quiet.step (ih (pc + 1) pos' _ ?_ ⟨a, ?_, hah, hacode⟩)
            · exact hempty
            · rcases Nat.eq_or_lt_of_le hpa with rfl | h
              · exact absurd hacode hisacc
              · omega
          · rw [heq]
            exact btFail_charged hempty _ hvis1
          · rw [heq]
            exact found_quiet hempty hvis1

/-- The nesting pass only ever answers a refusal, never `crOk`, so a program
`cert_shape` accepted is one it ran to the end. -/
theorem certShapeNest_refuses {regions : Array Region} :
    ∀ (fuel i : Nat) (ends : Array Nat) (v : Cr),
      certShapeNest regions i fuel ends = some v → v ≠ .crOk := by
  intro fuel
  induction fuel with
  | zero =>
      intro i ends v h
      exact absurd h (by simp [certShapeNest])
  | succ fuel ih =>
      intro i ends v h
      rw [certShapeNest] at h
      dsimp only at h
      split at h
      · simp only [Option.some.injEq] at h
        exact h ▸ (by decide)
      split at h
      · simp only [Option.some.injEq] at h
        exact h ▸ (by decide)
      split at h
      · simp only [Option.some.injEq] at h
        exact h ▸ (by decide)
      split at h
      · simp only [Option.some.injEq] at h
        exact h ▸ (by decide)
      split at h
      · simp only [Option.some.injEq] at h
        exact h ▸ (by decide)
      split at h
      · simp only [Option.some.injEq] at h
        exact h ▸ (by decide)
      exact ih (i + 1) _ v h

/-- What the nesting pass established about every region it walked: its
parent comes before it, its range is not backwards, and it sits inside its
parent's. -/
theorem certShapeNest_facts {regions : Array Region} :
    ∀ (fuel i : Nat) (ends : Array Nat),
      certShapeNest regions i fuel ends = none →
      ∀ j, i ≤ j → j < i + fuel →
        (regions[j]!).parent < j ∧ (regions[j]!).lo ≤ (regions[j]!).hi ∧
          (regions[(regions[j]!).parent]!).lo ≤ (regions[j]!).lo ∧
          (regions[j]!).hi ≤ (regions[(regions[j]!).parent]!).hi := by
  intro fuel
  induction fuel with
  | zero =>
      intro i ends h j h1 h2
      omega
  | succ fuel ih =>
      intro i ends h j h1 h2
      rw [certShapeNest] at h
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      rename_i hpar
      split at h
      · exact absurd h (by simp)
      rename_i hrange
      split at h
      · exact absurd h (by simp)
      rename_i hnest
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · simp only [not_or, Nat.not_lt] at hnest
        exact ⟨by omega, by omega, hnest.1, hnest.2⟩
      · exact ih (i + 1) _ h j (by omega) (by omega)

/-- The root's own clauses of `cert_shape`: the tree has a root, it is the
kind it says, and its range is the whole program. -/
theorem certShape_root {re : Re} (h : certShape re = .crOk) :
    0 < re.regions.size ∧ (re.regions[0]!).kind = .root ∧
      (re.regions[0]!).lo = 0 ∧ (re.regions[0]!).hi = re.code.size := by
  simp only [certShape] at h
  split at h
  · exact absurd h (by decide)
  rename_i hz
  split at h
  · exact absurd h (by decide)
  rename_i hk
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  rename_i hr
  simp only [not_or, Decidable.not_not] at hk hr
  exact ⟨by omega, hk, hr.1, hr.2⟩

/-- A program `cert_shape` accepted ran its nesting pass to the end. -/
theorem certShape_nest {re : Re} (h : certShape re = .crOk) :
    certShapeNest re.regions 1 (re.regions.size - 1)
      (re.regions.map (·.lo)) = none := by
  simp only [certShape] at h
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · rename_i v heq
    exact absurd h (certShapeNest_refuses _ _ _ _ heq)
  · rename_i heq
    exact heq

/-- And so every region but the root comes after its parent and sits inside
it. -/
theorem certShape_facts {re : Re} (h : certShape re = .crOk) (i : Nat)
    (h1 : 1 ≤ i) (h2 : i < re.regions.size) :
    (re.regions[i]!).parent < i ∧ (re.regions[i]!).lo ≤ (re.regions[i]!).hi ∧
      (re.regions[(re.regions[i]!).parent]!).lo ≤ (re.regions[i]!).lo ∧
      (re.regions[i]!).hi ≤ (re.regions[(re.regions[i]!).parent]!).hi :=
  certShapeNest_facts _ 1 _ (certShape_nest h) i h1 (by omega)

/-- Reading a `set!` back at an index it did not write. -/
theorem getElem!_set!_ne (a : Array Nat) (i v j : Nat) (hne : j ≠ i) :
    (a.set! i v)[j]! = a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.set! i v) j (by simpa using hj), getElem!_pos a j hj]
    exact Array.getElem_setIfInBounds_ne hj (fun hh => hne hh.symm)
  · rw [getElem!_neg (a.set! i v) j (by simpa using hj), getElem!_neg a j hj]

/-- And at the index it did. -/
theorem getElem!_set!_self (a : Array Nat) (i v : Nat) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  simp [h]

/-- Every entry of a fresh child list is the sentinel. -/
theorem getElem!_replicate_none (n j : Nat) (h : j < n) :
    (Array.replicate n none32)[j]! = none32 := by
  rw [getElem!_pos (Array.replicate n none32) j (by simpa using h)]
  simp

/-- What `region_kids` maintains: a child list hangs off the region that is
really the parent, and a sibling chain stays inside one parent's children.
Both are what makes the walk of a region meet only regions the nesting pass
has already put after it. -/
def KidsOk (regions : Array Region) (kids sibs : Array Nat) : Prop :=
  (∀ p, p < regions.size → kids[p]! ≠ none32 →
      1 ≤ kids[p]! ∧ kids[p]! < regions.size ∧
        (regions[kids[p]!]!).parent = p) ∧
    (∀ c, c < regions.size → sibs[c]! ≠ none32 →
      1 ≤ sibs[c]! ∧ sibs[c]! < regions.size ∧
        (regions[sibs[c]!]!).parent = (regions[c]!).parent)

/-- The backwards pass keeps it: each region it meets is filed under its own
parent, and the sibling it displaces was filed under the same one. -/
theorem regionKidsGo_ok {regions : Array Region}
    (hord : ∀ i, 1 ≤ i → i < regions.size → (regions[i]!).parent < i) :
    ∀ (k : Nat) (kids sibs : Array Nat), k < regions.size →
      kids.size = regions.size → sibs.size = regions.size →
      KidsOk regions kids sibs →
      KidsOk regions (regionKidsGo regions k kids sibs).1
        (regionKidsGo regions k kids sibs).2 := by
  intro k
  induction k with
  | zero =>
      intro kids sibs _ _ _ hok
      exact hok
  | succ k ih =>
      intro kids sibs hk hkids hsibs hok
      rw [regionKidsGo]
      have hpar : (regions[k + 1]!).parent < k + 1 :=
        hord (k + 1) (by omega) hk
      refine ih _ _ (by omega) (by simp [hkids]) (by simp [hsibs]) ⟨?_, ?_⟩
      · intro p hp hne
        by_cases hpe : p = (regions[k + 1]!).parent
        · subst hpe
          rw [getElem!_set!_self _ _ _ (by omega)]
          exact ⟨by omega, by omega, rfl⟩
        · rw [getElem!_set!_ne _ _ _ _ hpe] at hne ⊢
          exact hok.1 p hp hne
      · intro c hc hne
        by_cases hce : c = k + 1
        · subst hce
          rw [getElem!_set!_self _ _ _ (by omega)] at hne ⊢
          by_cases hkp : kids[(regions[k + 1]!).parent]! = none32
          · exact absurd hkp hne
          · obtain ⟨h0, h1, h2⟩ := hok.1 _ (by omega) hkp
            exact ⟨h0, h1, by rw [h2]⟩
        · rw [getElem!_set!_ne _ _ _ _ hce] at hne ⊢
          obtain ⟨h0, h1, h2⟩ := hok.2 c hc hne
          refine ⟨h0, h1, ?_⟩
          rw [h2]

/-- `region_kids` itself, read the same way. -/
theorem regionKids_ok {regions : Array Region} (hpos : 0 < regions.size)
    (hord : ∀ i, 1 ≤ i → i < regions.size → (regions[i]!).parent < i) :
    KidsOk regions (regionKids regions).1 (regionKids regions).2 := by
  rw [regionKids]
  refine regionKidsGo_ok hord _ _ _ (by omega) (by simp) (by simp) ⟨?_, ?_⟩
  · intro p hp hne
    exact absurd (getElem!_replicate_none _ _ hp) hne
  · intro c hc hne
    exact absurd (getElem!_replicate_none _ _ hc) hne

/-- The cursors a region's own walk may meet: the sentinel, or a region the
nesting pass put after it and filed under it. This is the predicate
`scanSpanGo_children` carries, and what makes an induction over the tree fall
— every child has a larger index than its parent. -/
def ChildOf (regions : Array Region) (i c : Nat) : Prop :=
  c = none32 ∨ (i < c ∧ c < regions.size ∧ (regions[c]!).parent = i)

/-- The first child of a region is one of its children. -/
theorem regionKids_first {regions : Array Region} (hpos : 0 < regions.size)
    (hord : ∀ i, 1 ≤ i → i < regions.size → (regions[i]!).parent < i)
    (i : Nat) (hi : i < regions.size) :
    ChildOf regions i (regionKids regions).1[i]! := by
  by_cases hne : (regionKids regions).1[i]! = none32
  · exact Or.inl hne
  · obtain ⟨h0, h1, h2⟩ := (regionKids_ok hpos hord).1 i hi hne
    exact Or.inr ⟨by have := hord _ h0 h1; omega, h1, h2⟩

/-- And so is the next one along the chain. -/
theorem regionKids_next {regions : Array Region} (hpos : 0 < regions.size)
    (hord : ∀ i, 1 ≤ i → i < regions.size → (regions[i]!).parent < i)
    (i c : Nat) (h : ChildOf regions i c) (hne : c ≠ none32) :
    ChildOf regions i (regionKids regions).2[c]! := by
  rcases h with rfl | ⟨-, hc, hpar⟩
  · exact absurd rfl hne
  · by_cases hs : (regionKids regions).2[c]! = none32
    · exact Or.inl hs
    · obtain ⟨h0, h1, h2⟩ := (regionKids_ok hpos hord).2 c hc hs
      rw [hpar] at h2
      exact Or.inr ⟨by have := hord _ h0 h1; omega, h1, h2⟩

/-- A tree of one region has no children to walk into. -/
theorem regionKids_single {regions : Array Region} (h : regions.size = 1) :
    regionKids regions = (Array.replicate 1 none32, Array.replicate 1 none32) := by
  rw [regionKids, h]
  rfl

/-- One step of the checker's induction over the regions, on a region whose
kind makes it a straight-line range: the walk over its own range accepted,
its claim dominates what the walk produced, and the induction went on to the
next region with a clean flag. -/
theorem certCheckRegions_step {re : Re} {prices : Array Price}
    {kids sibs : Array Nat} {i fuel : Nat} {over over' : Bool}
    (hkind : (re.regions[i]!).kind = .root ∨ (re.regions[i]!).kind = .group ∨
      (re.regions[i]!).kind = .branch)
    (h : certCheckRegions re prices kids sibs i (fuel + 1) over =
      (.crOk, over')) :
    (∃ acc : Acc,
        scanSpan re.code re.regions prices sibs (re.regions[i]!).lo
            (re.regions[i]!).hi kids[i]! (Acc.fresh (Poly.const 1)) over =
          (.crOk, acc, false) ∧ polyGe (prices[i]!).work acc.work = true ∧
          polyGe (prices[i]!).outs acc.flow = true) ∧
      certCheckRegions re prices kids sibs (i + 1) fuel false =
        (.crOk, over') := by
  rw [certCheckRegions] at h
  dsimp only at h
  rcases hkind with hk | hk | hk
  all_goals rw [hk] at h
  all_goals dsimp only at h
  all_goals
    (split at h
     · rename_i hv
       exact absurd h (by rw [Prod.mk.injEq]; simp [hv])
     rename_i hv
     split at h
     · exact absurd h (by simp)
     rename_i hover
     split at h
     · exact absurd h (by simp)
     rename_i hwork
     split at h
     · exact absurd h (by simp)
     rename_i houts
     split at h
     · exact absurd h (by simp)
     split at h
     · exact absurd h (by simp)
     rw [Bool.not_eq_true, Bool.not_eq_false'] at hwork houts
     rw [Bool.not_eq_true] at hover
     simp only [Decidable.not_not] at hv
     rw [hover] at h
     refine ⟨⟨_, ?_, hwork, houts⟩, h⟩
     rw [← hv, ← hover])

/-- The composition, for a program the compiler emitted one region for:
BOUNDS.md section 4.1 against the VM's own steps. A tree of one region is a
pattern with no group, no alternation and no repetition — a straight line of
tests and assertions — and on one the checker's walk and the run agree
instruction for instruction.

`hreach` is the one thing the checker does not ask about and the accounting
needs: some Accept inside the program, so the attempt ends inside it rather
than walking off the end of the code. Every program the compiler emits ends
in one. -/
theorem attemptsWithin_straight {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (hone : re.regions.size = 1)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size) := by
  obtain ⟨-, -, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨-, hkind, hlo, hhi⟩ := certShape_root hshape
  rw [regionKids_single hone, hone] at hregions
  obtain ⟨⟨acc, hscan, hdom, -⟩, -⟩ := certCheckRegions_step (Or.inl hkind) hregions
  rw [hlo, hhi, show ((Array.replicate 1 none32)[0]! : Nat) = none32 from rfl]
    at hscan
  obtain ⟨hloose, -, hvis⟩ :=
    scanSpanGo_straight (n := s.size) re.code.size 0 (by omega) _ _ _ _ hscan rfl
  simp only [Acc.fresh, Poly.val_zero, Poly.val_const] at hvis
  have hwork : visitCount re.code re.code.size 0 ≤
      (cert.prices[0]!).work.val s.size := by
    have := polyGe_sound hdom s.size
    omega
  obtain ⟨a, ha, hacode⟩ := hreach
  intro attempt fuel st hbt htrail hbtcap htrcap hmem
  have hempty : st.bt.size = 0 := by rw [hbt]; rfl
  have hq := btStep_quiet (re := re) (s := s) (mo := mo) (lim := lim)
    (start := start) (attempt := attempt)
    (fun q hq => hloose q (Nat.zero_le _) hq) fuel 0 attempt st hempty
    ⟨a, Nat.zero_le _, ha, hacode⟩
  have hres : (btStep re s mo lim start attempt fuel 0 attempt st).state.reserved =
      st.reserved := by
    simp only [BtSt.reserved, hq.btCap, hq.trailCap]
  have hcost := hq.cost
  have hmem' := hq.mem
  have hpeak := hq.peak
  have hdeep := hq.deepest
  exact ⟨by omega, hq.btCap ▸ hbtcap, hq.trailCap ▸ htrcap,
    by rw [hmem', hmem, hres], by omega, by omega⟩

/-- The children lists of a tree of two regions: the root has the one child,
and the child has none. -/
theorem regionKids_pair {regions : Array Region} (h : regions.size = 2)
    (hparent : (regions[1]!).parent = 0) :
    regionKids regions = (#[1, none32], #[none32, none32]) := by
  rw [regionKids, h]
  simp only [regionKidsGo, hparent]
  rfl

/-- The composition with a child in it: a group inside the root. The walk
charges the flow times what the group claims and jumps to its end, and the
group's own walk is the childless one already proved, so the two compose in
one step — which is the shape every deeper nest will reuse.

Where the child sits is not assumed: `cert_shape`'s nesting pass has
already put it after the root and inside its range. -/
theorem attemptsWithin_group {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (htwo : re.regions.size = 2)
    (hkind : (re.regions[1]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size) := by
  obtain ⟨-, -, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨-, hkind0, hlo, hhi⟩ := certShape_root hshape
  obtain ⟨hord, -, -, hin⟩ := certShape_facts hshape 1 (Nat.le_refl _) (by omega)
  have hparent : (re.regions[1]!).parent = 0 := by omega
  have hnest : (re.regions[1]!).hi ≤ re.code.size := by
    rw [hparent] at hin
    omega
  rw [regionKids_pair htwo hparent, htwo] at hregions
  dsimp only at hregions
  obtain ⟨⟨acc0, hscan0, hdom0, -⟩, hrest⟩ :=
    certCheckRegions_step (Or.inl hkind0) hregions
  obtain ⟨⟨acc1, hscan1, hdom1, houts1⟩, -⟩ :=
    certCheckRegions_step (Or.inr (Or.inl hkind)) hrest
  -- the group's own range, walked with no children of its own
  rw [show ((#[1, none32] : Array Nat)[1]! : Nat) = none32 from rfl] at hscan1
  obtain ⟨hloose1, -, hvis1, hflow1⟩ :=
    scanSpanGo_straight (n := s.size) (re.regions[1]!).hi (re.regions[1]!).lo
      (by omega) _ _ _ _ hscan1 rfl
  simp only [Acc.fresh, Poly.val_zero, Poly.val_const] at hvis1
  -- what the root's walk may charge at that child
  have hkid : ∀ c : Nat, (c = 1 ∨ c = none32) → c ≠ none32 →
      (re.regions[c]!).lo < (re.regions[c]!).hi →
      visitCount re.code (re.regions[c]!).hi (re.regions[c]!).lo ≤
          (cert.prices[c]!).work.val s.size ∧
        (∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi →
          (re.code[q]!).op.loose = true) ∧
        ((∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi →
          (re.code[q]!).op ≠ .accept) → 1 ≤ (cert.prices[c]!).outs.val s.size) ∧
        (re.regions[c]!).hi ≤ re.code.size := by
    intro c hP hne _
    rcases hP with rfl | rfl
    · refine ⟨?_, fun q h1 h2 => hloose1 q h1 h2, ?_, hnest⟩
      · have := polyGe_sound hdom1 s.size
        omega
      · intro hno
        have hout := polyGe_sound houts1 s.size
        rw [hflow1 hno] at hout
        simp only [Acc.fresh, Poly.val_const] at hout
        omega
    · exact absurd rfl hne
  obtain ⟨hloose, -, hvis⟩ :=
    scanSpanGo_children (n := s.size) (sibs := #[none32, none32])
      (fun c => c = 1 ∨ c = none32)
      (fun c hP hne => by
        rcases hP with rfl | rfl
        · exact Or.inr rfl
        · exact absurd rfl hne)
      hkid re.code.size 0 1 (Or.inl rfl) (by omega) _ _ _ _
      (by rw [hlo, hhi] at hscan0
          rw [show ((#[1, none32] : Array Nat)[0]! : Nat) = 1 from rfl] at hscan0
          exact hscan0) rfl
  simp only [Acc.fresh, Poly.val_zero, Poly.val_const] at hvis
  have hwork : visitCount re.code re.code.size 0 ≤
      (cert.prices[0]!).work.val s.size := by
    have := polyGe_sound hdom0 s.size
    omega
  obtain ⟨a, ha, hacode⟩ := hreach
  intro attempt fuel st hbt htrail hbtcap htrcap hmem
  have hempty : st.bt.size = 0 := by rw [hbt]; rfl
  have hq := btStep_quiet (re := re) (s := s) (mo := mo) (lim := lim)
    (start := start) (attempt := attempt)
    (fun q hq => hloose q (Nat.zero_le _) hq) fuel 0 attempt st hempty
    ⟨a, Nat.zero_le _, ha, hacode⟩
  have hres : (btStep re s mo lim start attempt fuel 0 attempt st).state.reserved =
      st.reserved := by
    simp only [BtSt.reserved, hq.btCap, hq.trailCap]
  have hcost := hq.cost
  have hmem' := hq.mem
  have hpeak := hq.peak
  have hdeep := hq.deepest
  exact ⟨by omega, hq.btCap ▸ hbtcap, hq.trailCap ▸ htrcap,
    by rw [hmem', hmem, hres], by omega, by omega⟩

/-! ### R-6, R-7 and R-8 with nothing assumed, on a program of one region -/

/-- R-6 for a pattern with no group, no alternation and no repetition: the
cost a run charges is at most the certificate's, and no hypothesis is left
over. -/
theorem btRun_cost_le_straight {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (hone : re.regions.size = 1)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size :=
  btRun_cost_le hcert (attemptsWithin_straight hcert hone hreach)

/-- R-7 on the same programs. Nothing forks, so the stack never leaves the
ground. -/
theorem btRun_stack_le_straight {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (hone : re.regions.size = 1)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  btRun_stack_le (attemptsWithin_straight hcert hone hreach)

/-- And R-8. -/
theorem btRun_mem_le_straight {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (hone : re.regions.size = 1)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size :=
  btRun_mem_le hcert (attemptsWithin_straight hcert hone hreach)

/-! ### And on a program of a root with one group in it -/

/-- R-6 for a pattern that is one group inside a straight line, again with
nothing assumed about the run. -/
theorem btRun_cost_le_group {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (htwo : re.regions.size = 2)
    (hkind : (re.regions[1]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size :=
  btRun_cost_le hcert (attemptsWithin_group hcert htwo hkind hreach)

/-- R-7 on the same programs. -/
theorem btRun_stack_le_group {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (htwo : re.regions.size = 2)
    (hkind : (re.regions[1]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  btRun_stack_le (attemptsWithin_group hcert htwo hkind hreach)

/-- And R-8. -/
theorem btRun_mem_le_group {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk) (htwo : re.regions.size = 2)
    (hkind : (re.regions[1]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size :=
  btRun_mem_le hcert (attemptsWithin_group hcert htwo hkind hreach)

/-! ### The same three, as the accessors report them -/

/-- An accessor that answered a number answered the bound's value at that
length: the ceiling test only ever turns a number into a refusal. -/
theorem certBound_cost_val {cert : Cert} {n v : Nat}
    (h : certBound cert .cost n = ⟨true, v⟩) : v = cert.cost.val n := by
  simp only [certBound] at h
  split at h
  · exact absurd h (by simp [Bound.exceeds])
  · exact polyValue_ok h

theorem certBound_stack_val {cert : Cert} {n v : Nat}
    (h : certBound cert .stack n = ⟨true, v⟩) : v = cert.stack.val n := by
  simp only [certBound] at h
  split at h
  · exact absurd h (by simp [Bound.exceeds])
  · exact polyValue_ok h

theorem certBound_mem_val {cert : Cert} {n v : Nat}
    (h : certBound cert .mem n = ⟨true, v⟩) : v = cert.mem.val n := by
  simp only [certBound] at h
  split at h
  · exact absurd h (by simp [Bound.exceeds])
  · exact polyValue_ok h

/-- R-6 as a caller reads it: the cost accessor's own number bounds the
run. -/
theorem btRun_cost_le_bound {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start v : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hatt : AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size))
    (hb : certBound cert .cost s.size = ⟨true, v⟩) :
    (btRun re s start mo lim 0 0).usage.cost ≤ v := by
  rw [certBound_cost_val hb]
  exact btRun_cost_le hcert hatt

/-- R-7, the same way. -/
theorem btRun_stack_le_bound {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start v : Nat} {cert : Cert}
    (hatt : AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size))
    (hb : certBound cert .stack s.size = ⟨true, v⟩) :
    (btRun re s start mo lim 0 0).usage.stack ≤ v := by
  rw [certBound_stack_val hb]
  exact btRun_stack_le hatt

/-- And R-8. -/
theorem btRun_mem_le_bound {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start v : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hatt : AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size))
    (hb : certBound cert .mem s.size = ⟨true, v⟩) :
    (btRun re s start mo lim 0 0).usage.mem ≤ v := by
  rw [certBound_mem_val hb]
  exact btRun_mem_le hcert hatt

/-! ## The whole-call guards (S-10, the part that is about the totals) -/

/-- A caller whose budget sits at or above the certificate's numbers gets
past the setup guard: the register file and the ovector are inside both the
cost and the memory limit, because the certificate paid for them and more.
The refusals the attempts themselves can make are the other half of S-10 and
wait on `AttemptsWithin`. -/
theorem btRun_setup_ok {re : Re} {cert : Cert} {lim : Limits} {n : Nat}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hcost : cert.cost.val n ≤ lim.cost) (hmem : cert.mem.val n ≤ lim.mem) :
    btSetup re ≤ lim.cost ∧ btSetup re ≤ lim.mem := by
  obtain ⟨hc, hm⟩ := certCheck_bt_dom hcert n
  exact ⟨by omega, by omega⟩

end Pcrevera.Ref
