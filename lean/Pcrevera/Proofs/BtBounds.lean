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

A nest of any depth is the third. The measure the tree induction spends is
`certShape_facts` — every region comes after its parent and sits inside its
range — together with `regionKids_ok`, which says the child lists really
hang off the region they are filed under: between them, every cursor a
region's walk can meet has a larger index than the region walking it, which
is what `ChildOf` states and what `region_visits` walks downwards.
`attemptsWithin_nest` therefore prices a whole tree of groups inside groups,
and R-6, R-7 and R-8 hold for such a program with nothing assumed but that
it contains an Accept.

R-9's second half falls out of the same reading. A straight-line run never
pushes, so neither array ever grows, whatever capacities the call started
with: `btRun_no_growth` says the peak it reports is the register file and the
ovector it was handed, which is "a call on a preallocated context allocates
nothing" for these programs.

So does S-10's. Every refusal in the engine is a pre-charge test, and on
these programs the only charges are the setup, one reset and one visit per
instruction at each starting position, and the delivery — all of which the
certificate paid for. `btRun_inBudget_nest` reads that back: a caller whose
cost and memory limits sit at or above the certificate's numbers never sees
ResourceExceeded. The stack limit does not appear, because nothing is ever
pushed on this path and so nothing can be refused for depth.

Alternation and repetition need more than any of this. The moment a program
forks, the backtrack stack stops being empty and the trail starts recording,
and reading the checker's count alongside the VM instruction for instruction
stops working — an attempt is then a depth-first traversal of everything the
splits left behind rather than a walk. The last three sections of this file
are what replaces it.

`Flow` and `btStep_priced` are the fork account, and they are the whole of
what the run side asks for. A *pricing* gives every program point what the
rest of the attempt may still visit, record and push, with a split's numbers
covering both of its arms; a run's debt is the pricing where it stands plus
the pricing at every resumption point on its stack; and no step raises it,
because a split moves its second arm's price onto the entry it pushes and a
pop moves it back. `attemptsWithin_of_flow` turns a pricing into
`AttemptsWithin`, so a program with one whose root claim dominates it gets
R-6, R-7 and R-8 from the composition above, on a caller whose memory limit
is inside the allocation ceiling.

`costAt` is where a pricing comes from: the code itself, one charge per
opcode, on a program whose control flow only ever moves forward.
`scanSpanGo_priced` is section 4.1 read against it — the flow arriving times
the pricing at the cursor, covered by what the walk accumulates plus the
flow leaving times the pricing at the end of the range — and
`scanAltGo_priced` is section 4.2, with `scan_alt` and `shape_alt` walked in
step so the branch list and the bytecode are held together.

`region_code_ok` reads the forwardness those two need off `cert_shape`'s own
walk, and `region_priced` composes them over the region tree: every region
comes after its parent, so walking the index downwards prices a region from
prices that are already there, and at the root the clause is the whole
program. `attemptsWithin_forward` joins that to the fork account, and R-6,
R-7 and R-8 follow for a tree of groups, alternations and optional items —
BOUNDS.md sections 4.1, 4.2 and 4.3.

Section 4.4 is where the code-level pricing genuinely stops. A counted
repetition's `RepNext` jumps back to its own head, so what is still to come
from that point depends on the counter and not on the program point alone,
and `costAt` would not even be well defined. That wants a pricing indexed by
more than the program point, which is a design step rather than another
rung, and it is honestly open.

One thing the checker does not ask about turns out to be load-bearing: that
the program cannot walk off the end of its own code. `cert_shape` admits a
straight-line region of tests with no Accept in it, and a run of one walks
straight past the last instruction — where the reference reads a default
and the real engine would read past its own array. Once alternation is in
the picture the same hole opens one level down, because a branch's closing
jump and a skipped optional body both target the end of their region.

So the theorems below carry it as two explicit hypotheses rather than
pretending otherwise: the program's last instruction is an `Accept`, and no
alternation and no optional item ends the program. Everything the compiler
emits satisfies both — it puts an `Accept` after the root and nothing after
that — and whether the checker should be refusing programs that do not is a
question for BOUNDS.md. Two more hypotheses are on the same footing and are
stated the same way: that every repeat region in the tree is an optional
item, which is where this pricing stops, and that the caller's memory limit
sits inside the allocation ceiling, which is what makes the growth schedule
double.

None of the four is read off an accepted certificate, and the theorems say
so in their own statements. What acceptance buys is everything else.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## The bound algebra, in the projection form a flag chain leaves behind -/

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
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
      cert.prices.size = re.regions.size ∧
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
  refine ⟨hst, htr, by simpa using hsize, ⟨over, by rw [hcharge]; simpa using hok⟩,
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

/-- `bt_run` with the bindings taken out: the two guards, the loop over the
starting positions, and the delivery a match pays for. The capacities are
whatever the caller handed in — nothing on this path cares whether they came
from a context or from the plain call. -/
theorem btRun_caps (re : Re) (s : ByteArray) (start : Nat) (mo : MOpts)
    (lim : Limits) (btCap trailCap : Nat) :
    btRun re s start mo lim btCap trailCap =
      if start > s.size then ⟨.badInput, #[], {}⟩
      else if btSetup re > lim.mem || btSetup re > lim.cost then
        ⟨.resourceExceeded, #[], {}⟩
      else
        match btLoop re s mo lim start (s.size + 1 - start) start
            ⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
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
  rw [btRun_caps]
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
  obtain ⟨hs, ht, -, ⟨over, hcharge⟩, -, -⟩ := certCheck_bt_spec h
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
          acc'.work.val n ∧
        ((∀ q, pc ≤ q → q < hi → (code[q]!).op ≠ .accept) →
          acc.flow.val n ≤ acc'.flow.val n) := by
  intro k
  induction k with
  | zero =>
      intro pc cursor hP hk acc acc' over over' h hover
      rw [scanSpanGo, dif_neg (by omega)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, hacc, hov⟩ := h
      subst hacc
      subst hov
      refine ⟨fun q h1 h2 => by omega, hover, ?_, fun _ => Nat.le_refl _⟩
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
          obtain ⟨hloose, hov, hwork, hflow⟩ :=
            ih (regions[cursor]!).hi (sibs[cursor]!) (hsib cursor hP hcond.1)
              (by omega) _ _ _ _ h hover
          dsimp only at hwork hflow
          have f6 := polyMul_snd hov
          have f5 := polyAdd_snd f6
          have f4 := polyMul_snd f5
          have f3 := polyAdd_snd f4
          have f2 := polyMul_snd f3
          have f1 := polyAdd_snd f2
          have vcw := polyMul_eq f1 n
          have vw := polyAdd_le f2 n
          have von := polyMul_eq hov n
          rw [von] at hwork hflow
          refine ⟨?_, polyMul_snd f1, ?_, ?_⟩
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
          · intro hno
            have hnokid : ∀ q, (regions[cursor]!).lo ≤ q →
                q < (regions[cursor]!).hi → (code[q]!).op ≠ .accept := by
              intro q h1 h2
              exact hno q (by rw [hcond.2] at h1; omega) (by omega)
            have houts := hcouts hnokid
            have hgrow : acc.flow.val n ≤
                acc.flow.val n * (prices[cursor]!).outs.val n :=
              Nat.le_mul_of_pos_right _ (by omega)
            have hih := hflow (fun q h1 h2 => hno q (by omega) h2)
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
              | (obtain ⟨hloose, hov, hwork, hflow⟩ :=
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
                 dsimp only at hwork hflow
                 refine ⟨?_, hov0, ?_, ?_⟩
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
        refine ⟨fun q h1 h2 => by omega, hover, ?_, fun _ => Nat.le_refl _⟩
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

/-- A triple read back off its own components, which is how a walk's answer
is turned into the existential below without naming the accumulator. -/
theorem triple_eq {α β γ : Type _} {x : α × β × γ} {a : α} {c : γ}
    (h1 : x.1 = a) (h2 : x.2.2 = c) : x = (a, x.2.1, c) := by
  obtain ⟨u, v, w⟩ := x
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- What the checker's induction settled at one region, whichever kind it
is: the walk that kind asks for accepted with a clean flag, and the region's
own claim dominates all four of the numbers that came out.

Reading all four matters here in a way it did not before. A program that
never forks pushes nothing and records nothing, so `stack` and `trail` were
free; once one does, the pricing wants those two claims as much as it wants
`work`, and the checker has been testing them all along. -/
def RegionPriced (re : Re) (prices : Array Price) (kids sibs : Array Nat)
    (i : Nat) : Prop :=
  ∃ acc : Acc,
    (match (re.regions[i]!).kind with
      | .root | .group | .branch =>
          scanSpan re.code re.regions prices sibs (re.regions[i]!).lo
            (re.regions[i]!).hi kids[i]! (Acc.fresh (Poly.const 1)) false
      | .alt => scanAlt prices sibs kids[i]! false
      | .«repeat» =>
          scanRepeat re.code re.reps re.regions prices sibs i kids[i]! false) =
        (.crOk, acc, false) ∧
      polyGe (prices[i]!).work acc.work = true ∧
        polyGe (prices[i]!).outs acc.flow = true ∧
        polyGe (prices[i]!).stack acc.stack = true ∧
        polyGe (prices[i]!).trail acc.trail = true

/-- One step of the checker's induction over the regions: the walk over this
region accepted, its claim dominates what the walk produced, and the
induction went on to the next region with a clean flag. The kind does not
appear — every arm of the dispatch is answered the same way. -/
theorem certCheckRegions_step {re : Re} {prices : Array Price}
    {kids sibs : Array Nat} {i fuel : Nat} {over' : Bool}
    (h : certCheckRegions re prices kids sibs i (fuel + 1) false =
      (.crOk, over')) :
    RegionPriced re prices kids sibs i ∧
      certCheckRegions re prices kids sibs (i + 1) fuel false =
        (.crOk, over') := by
  rw [certCheckRegions] at h
  dsimp only at h
  unfold RegionPriced
  cases hk : (re.regions[i]!).kind
  all_goals rw [hk] at h
  all_goals dsimp only at h ⊢
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
     rename_i hstack
     split at h
     · exact absurd h (by simp)
     rename_i htrail
     rw [Bool.not_eq_true, Bool.not_eq_false'] at hwork houts hstack htrail
     rw [Bool.not_eq_true] at hover
     simp only [Decidable.not_not] at hv
     rw [hover] at h
     exact ⟨⟨_, triple_eq hv hover, hwork, houts, hstack, htrail⟩, h⟩)

/-- A straight-line region's reading of it. -/
theorem RegionPriced.span {re : Re} {prices : Array Price}
    {kids sibs : Array Nat} {i : Nat}
    (hkind : (re.regions[i]!).kind = .root ∨ (re.regions[i]!).kind = .group ∨
      (re.regions[i]!).kind = .branch)
    (h : RegionPriced re prices kids sibs i) :
    ∃ acc : Acc,
      scanSpan re.code re.regions prices sibs (re.regions[i]!).lo
          (re.regions[i]!).hi kids[i]! (Acc.fresh (Poly.const 1)) false =
        (.crOk, acc, false) ∧ polyGe (prices[i]!).work acc.work = true ∧
        polyGe (prices[i]!).outs acc.flow = true ∧
        polyGe (prices[i]!).stack acc.stack = true ∧
        polyGe (prices[i]!).trail acc.trail = true := by
  unfold RegionPriced at h
  rcases hkind with hk | hk | hk
  all_goals rw [hk] at h
  all_goals exact h

/-- And an alternation's. -/
theorem RegionPriced.alt {re : Re} {prices : Array Price}
    {kids sibs : Array Nat} {i : Nat} (hkind : (re.regions[i]!).kind = .alt)
    (h : RegionPriced re prices kids sibs i) :
    ∃ acc : Acc,
      scanAlt prices sibs kids[i]! false = (.crOk, acc, false) ∧
        polyGe (prices[i]!).work acc.work = true ∧
        polyGe (prices[i]!).outs acc.flow = true ∧
        polyGe (prices[i]!).stack acc.stack = true ∧
        polyGe (prices[i]!).trail acc.trail = true := by
  unfold RegionPriced at h
  rw [hkind] at h
  exact h

/-- And a repetition's. -/
theorem RegionPriced.rep {re : Re} {prices : Array Price}
    {kids sibs : Array Nat} {i : Nat}
    (hkind : (re.regions[i]!).kind = .«repeat»)
    (h : RegionPriced re prices kids sibs i) :
    ∃ acc : Acc,
      scanRepeat re.code re.reps re.regions prices sibs i kids[i]! false =
        (.crOk, acc, false) ∧
        polyGe (prices[i]!).work acc.work = true ∧
        polyGe (prices[i]!).outs acc.flow = true ∧
        polyGe (prices[i]!).stack acc.stack = true ∧
        polyGe (prices[i]!).trail acc.trail = true := by
  unfold RegionPriced at h
  rw [hkind] at h
  exact h

/-- Every region the checker priced, priced. The checker's induction runs
forwards over the region table, so this is that same walk read off at each
index. -/
theorem certCheckRegions_all {re : Re} {prices : Array Price}
    {kids sibs : Array Nat} :
    ∀ (fuel i : Nat) (over' : Bool),
      certCheckRegions re prices kids sibs i fuel false = (.crOk, over') →
      ∀ j, i ≤ j → j < i + fuel → RegionPriced re prices kids sibs j := by
  intro fuel
  induction fuel with
  | zero =>
      intro i over' h j h1 h2
      omega
  | succ fuel ih =>
      intro i over' h j h1 h2
      obtain ⟨hstep, hnext⟩ := certCheckRegions_step h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hstep
      · exact ih (i + 1) over' hnext j (by omega) (by omega)

/-- The tree induction, spending the measure: what one region's claim is
worth follows from what the regions after it are worth, and every child of a
region comes after it. Walking the index downwards therefore prices the
whole tree, however deep the nest of straight-line regions goes. -/
theorem region_visits {re : Re} {prices : Array Price} {n : Nat}
    (hpos : 0 < re.regions.size)
    (hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i)
    (hfacts : ∀ i, 1 ≤ i → i < re.regions.size →
      (re.regions[i]!).hi ≤ (re.regions[(re.regions[i]!).parent]!).hi)
    (hscan : ∀ j, j < re.regions.size → ∃ acc : Acc,
      scanSpan re.code re.regions prices (regionKids re.regions).2
          (re.regions[j]!).lo (re.regions[j]!).hi (regionKids re.regions).1[j]!
          (Acc.fresh (Poly.const 1)) false = (.crOk, acc, false) ∧
        polyGe (prices[j]!).work acc.work = true ∧
        polyGe (prices[j]!).outs acc.flow = true) :
    ∀ (k i : Nat), re.regions.size - i ≤ k → i < re.regions.size →
      visitCount re.code (re.regions[i]!).hi (re.regions[i]!).lo ≤
          (prices[i]!).work.val n ∧
        (∀ q, (re.regions[i]!).lo ≤ q → q < (re.regions[i]!).hi →
          (re.code[q]!).op.loose = true) ∧
        ((∀ q, (re.regions[i]!).lo ≤ q → q < (re.regions[i]!).hi →
          (re.code[q]!).op ≠ .accept) → 1 ≤ (prices[i]!).outs.val n) := by
  intro k
  induction k with
  | zero =>
      intro i hk hi
      omega
  | succ k ih =>
      intro i hk hi
      have hkid : ∀ c, ChildOf re.regions i c → c ≠ none32 →
          (re.regions[c]!).lo < (re.regions[c]!).hi →
          visitCount re.code (re.regions[c]!).hi (re.regions[c]!).lo ≤
              (prices[c]!).work.val n ∧
            (∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi →
              (re.code[q]!).op.loose = true) ∧
            ((∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi →
              (re.code[q]!).op ≠ .accept) → 1 ≤ (prices[c]!).outs.val n) ∧
            (re.regions[c]!).hi ≤ (re.regions[i]!).hi := by
        intro c hP hne _
        rcases hP with rfl | ⟨hic, hcs, hpar⟩
        · exact absurd rfl hne
        · obtain ⟨h1, h2, h3⟩ := ih c (by omega) hcs
          refine ⟨h1, h2, h3, ?_⟩
          have hle := hfacts c (by omega) hcs
          rw [hpar] at hle
          exact hle
      obtain ⟨acci, hscani, hdomw, hdomo⟩ := hscan i hi
      obtain ⟨hloose, -, hvis, hflow⟩ :=
        scanSpanGo_children (n := n) (ChildOf re.regions i)
          (fun c hP hne => regionKids_next hpos hord i c hP hne) hkid
          (re.regions[i]!).hi (re.regions[i]!).lo
          ((regionKids re.regions).1[i]!) (regionKids_first hpos hord i hi)
          (by omega) _ _ _ _ hscani rfl
      simp only [Acc.fresh, Poly.val_zero, Poly.val_const] at hvis hflow
      refine ⟨?_, hloose, ?_⟩
      · have := polyGe_sound hdomw n
        omega
      · intro hno
        have h1 := polyGe_sound hdomo n
        have h2 := hflow hno
        omega

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
  obtain ⟨-, -, -, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨-, hkind, hlo, hhi⟩ := certShape_root hshape
  rw [regionKids_single hone, hone] at hregions
  obtain ⟨acc, hscan, hdom, -, -, -⟩ :=
    (certCheckRegions_step hregions).1.span (Or.inl hkind)
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
  obtain ⟨-, -, -, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨-, hkind0, hlo, hhi⟩ := certShape_root hshape
  obtain ⟨hord, -, -, hin⟩ := certShape_facts hshape 1 (Nat.le_refl _) (by omega)
  have hparent : (re.regions[1]!).parent = 0 := by omega
  have hnest : (re.regions[1]!).hi ≤ re.code.size := by
    rw [hparent] at hin
    omega
  rw [regionKids_pair htwo hparent, htwo] at hregions
  dsimp only at hregions
  obtain ⟨hroot, hrest⟩ := certCheckRegions_step hregions
  obtain ⟨acc0, hscan0, hdom0, -, -, -⟩ := hroot.span (Or.inl hkind0)
  obtain ⟨acc1, hscan1, hdom1, houts1, -, -⟩ :=
    (certCheckRegions_step hrest).1.span (Or.inr (Or.inl hkind))
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

/-- What the checker's walk is worth on a program whose regions are all
straight-line ranges: the root's claim covers the visits of one attempt, and
every instruction in the program is one a region may hold loose. -/
theorem nest_priced {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group) (n : Nat) :
    visitCount re.code re.code.size 0 ≤ (cert.prices[0]!).work.val n ∧
      ∀ q, q < re.code.size → (re.code[q]!).op.loose = true := by
  obtain ⟨-, -, -, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨hpos, hkind0, hlo, hhi⟩ := certShape_root hshape
  have hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i :=
    fun i h1 h2 => (certShape_facts hshape i h1 h2).1
  have hnest : ∀ i, 1 ≤ i → i < re.regions.size →
      (re.regions[i]!).hi ≤ (re.regions[(re.regions[i]!).parent]!).hi :=
    fun i h1 h2 => (certShape_facts hshape i h1 h2).2.2.2
  have hscan := certCheckRegions_all re.regions.size 0 over hregions
  obtain ⟨hwork, hloose, -⟩ := region_visits (n := n) hpos hord hnest
    (fun j hj =>
      ((hscan j (Nat.zero_le _) (by omega)).span
        ((hkinds j hj).imp id Or.inl)).imp
        (fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩))
    re.regions.size 0 (by omega) hpos
  rw [hlo, hhi] at hwork hloose
  exact ⟨hwork, fun q hq => hloose q (Nat.zero_le _) hq⟩

/-- The composition at any depth: a region tree of groups inside groups.
Every region is a straight-line range, so every one of them is priced by the
walk of section 4.1, and the tree induction above turns the root's claim into
a bound on what one attempt visits. This subsumes the two cases above; they
are kept because they are the worked instances the general proof was read
off. -/
theorem attemptsWithin_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size) := by
  obtain ⟨hwork, hloose⟩ := nest_priced hcert hkinds s.size
  obtain ⟨a, ha, hacode⟩ := hreach
  intro attempt fuel st hbt htrail hbtcap htrcap hmem
  have hempty : st.bt.size = 0 := by rw [hbt]; rfl
  have hq := btStep_quiet (re := re) (s := s) (mo := mo) (lim := lim)
    (start := start) (attempt := attempt) hloose fuel 0 attempt st hempty
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

/-! ### R-6, R-7 and R-8 on a tree of groups, with nothing assumed -/

/-- R-6 for a pattern with groups but no alternation and no repetition,
nested as deep as it likes. -/
theorem btRun_cost_le_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size :=
  btRun_cost_le hcert (attemptsWithin_nest hcert hkinds hreach)

/-- R-7 on the same programs. -/
theorem btRun_stack_le_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  btRun_stack_le (attemptsWithin_nest hcert hkinds hreach)

/-- And R-8. -/
theorem btRun_mem_le_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size :=
  btRun_mem_le hcert (attemptsWithin_nest hcert hkinds hreach)

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

/-! ### R-9's second half: a call that allocates nothing -/

/-- Two quiet stretches in a row. -/
theorem Quiet.trans {a b : Nat} {st mid out : BtSt} (h₁ : Quiet a st mid)
    (h₂ : Quiet b mid out) : Quiet (a + b) st out := by
  obtain ⟨c₁, -, b₁, t₁, m₁, p₁, d₁⟩ := h₁
  obtain ⟨c₂, e₂, b₂, t₂, m₂, p₂, d₂⟩ := h₂
  exact ⟨by omega, e₂, by omega, by omega, by omega, by omega, by omega⟩

/-- The reset at a starting position charges, clears the register file and
truncates both arrays. It moves neither capacity, so it is quiet too. -/
theorem Quiet.reset {c r : Nat} {st out : BtSt} {regs : Array UInt32}
    (h : Quiet c ⟨regs, #[], st.btCap, #[], st.trailCap,
      ⟨st.m.cost + r, st.m.mem, st.m.peak⟩, st.stackpeak⟩ out) :
    Quiet (r + c) st out := by
  obtain ⟨hc, he, hb, ht, hm, hp, hd⟩ := h
  dsimp only at hc hb ht hm hp hd
  exact ⟨by omega, he, hb, ht, hm, hp, hd⟩

/-- Every attempt of a run is quiet: it charges, and moves nothing else. -/
def AttemptsQuiet (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start : Nat) : Prop :=
  ∀ (attempt fuel : Nat) (st : BtSt), st.bt.size = 0 →
    ∃ c, Quiet c st (btStep re s mo lim start attempt fuel 0 attempt st).state

/-- Quiet attempts make a quiet loop: whatever the run charges over the
starting positions, it never touches a capacity, the resident bytes or the
peak. -/
theorem btLoop_quiet {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} (hatt : AttemptsQuiet re s mo lim start) :
    ∀ (steps attempt : Nat) (st : BtSt), st.bt.size = 0 →
      ∃ c, Quiet c st (btLoop re s mo lim start steps attempt st).state := by
  intro steps
  induction steps with
  | zero =>
      intro attempt st hempty
      rw [btLoop]
      exact ⟨0, Quiet.still hempty⟩
  | succ steps ih =>
      intro attempt st hempty
      rw [btLoop_succ]
      split
      · exact ⟨0, Quiet.still hempty⟩
      · obtain ⟨c, hc⟩ := hatt attempt
          (lim.cost + 1 - (st.m.cost + re.nregs * regSize))
          ⟨Array.replicate re.nregs unset32, #[], st.btCap, #[], st.trailCap,
            ⟨st.m.cost + re.nregs * regSize, st.m.mem, st.m.peak⟩,
            st.stackpeak⟩ rfl
        split
        · rename_i endPos st' hout
          rw [hout] at hc
          simp only [AttemptOut.state] at hc
          exact ⟨_, Quiet.reset hc⟩
        · rename_i st' hout
          rw [hout] at hc
          simp only [AttemptOut.state] at hc
          exact ⟨_, Quiet.reset hc⟩
        · rename_i st' hout
          rw [hout] at hc
          simp only [AttemptOut.state] at hc
          split
          · exact ⟨_, Quiet.reset hc⟩
          · obtain ⟨c', hc'⟩ := ih _ st' hc.empty
            exact ⟨_, (Quiet.reset hc).trans hc'⟩

/-- R-9's second half for these programs: a call allocates nothing. Whatever
capacities it starts with — a preallocated context's reservation, or none at
all — neither array is ever pushed to, so neither ever grows and the peak the
call reports is the register file and the ovector it was handed. -/
theorem btRun_no_growth {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start btCap trailCap : Nat} (hatt : AttemptsQuiet re s mo lim start) :
    (btRun re s start mo lim btCap trailCap).usage.mem ≤ btSetup re := by
  rw [btRun_caps]
  split
  · exact Nat.zero_le _
  split
  · exact Nat.zero_le _
  obtain ⟨c, hc⟩ := btLoop_quiet hatt (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], btCap, #[], trailCap,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ rfl
  have hpeak := hc.peak
  dsimp only at hpeak
  split
  · rename_i st' hout
    rw [hout] at hpeak
    simp only [RunEnd.state] at hpeak
    split <;> simp only [BtSt.usage] <;> omega
  · rename_i st' hout
    rw [hout] at hpeak
    simp only [RunEnd.state] at hpeak
    simp only [BtSt.usage]
    omega
  · rename_i st' hout
    rw [hout] at hpeak
    simp only [RunEnd.state] at hpeak
    simp only [BtSt.usage]
    omega

/-- And every attempt of such a program is quiet, which is what R-9's second
half needs. -/
theorem attemptsQuiet_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    AttemptsQuiet re s mo lim start := by
  obtain ⟨-, hloose⟩ := nest_priced hcert hkinds 0
  obtain ⟨a, ha, hacode⟩ := hreach
  intro attempt fuel st hempty
  exact ⟨_, btStep_quiet hloose fuel 0 attempt st hempty
    ⟨a, Nat.zero_le _, ha, hacode⟩⟩

/-- R-9's second half on a tree of groups, with nothing assumed: such a call
never grows either scratch array, so a preallocated context hands out
capacity nobody spends. -/
theorem btRun_no_growth_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start btCap trailCap : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept) :
    (btRun re s start mo lim btCap trailCap).usage.mem ≤ btSetup re :=
  btRun_no_growth (attemptsQuiet_nest (cert := cert) hcert hkinds hreach)

/-! ### S-10 for these programs: no refusal on a budget that covers them -/

/-- An attempt that did not run out of budget. -/
def AttemptOut.inBudget : AttemptOut → Prop
  | .exceeded _ => False
  | _ => True

/-- The same for a whole call. -/
def RunEnd.inBudget : RunEnd → Prop
  | .exceeded _ => False
  | _ => True

/-- A failed path with nothing to backtrack to asks for nothing. -/
theorem btFail_inBudget {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel : Nat} {st : BtSt} (h : st.bt.size = 0) :
    (btFail re s mo lim start attempt fuel st).inBudget := by
  rw [btFail_empty h]
  trivial

/-- Every refusal inside an attempt is a pre-charge test, and on a
straight-line program the only charge is the per-visit unit — so a budget
that covers the visits is a budget the attempt never asks past. -/
theorem btStep_inBudget {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt : Nat}
    (hloose : ∀ q, q < re.code.size → (re.code[q]!).op.loose = true) :
    ∀ (fuel pc pos : Nat) (st : BtSt), st.bt.size = 0 →
      (∃ a, pc ≤ a ∧ a < re.code.size ∧ (re.code[a]!).op = .accept) →
      visitCount re.code re.code.size pc ≤ fuel →
      st.m.cost + visitCount re.code re.code.size pc ≤ lim.cost →
      (btStep re s mo lim start attempt fuel pc pos st).inBudget := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc pos st hempty hreach hfuel hbudget
      obtain ⟨a, hpa, hah, hacode⟩ := hreach
      rw [visitCount_succ re.code re.code.size pc (by omega)] at hfuel
      split at hfuel <;> omega
  | succ fuel ih =>
      intro pc pos st hempty hreach hfuel hbudget
      obtain ⟨a, hpa, hah, hacode⟩ := hreach
      have hpc : pc < re.code.size := by omega
      have hvis1 : 1 ≤ visitCount re.code re.code.size pc := by
        rw [visitCount_succ re.code re.code.size pc hpc]
        split <;> omega
      have hlim : ¬ st.m.cost ≥ lim.cost := by omega
      by_cases hisacc : (re.code[pc]!).op = .accept
      · rcases btStep_accept hisacc hlim with ⟨regs, heq⟩ | heq
        · rw [heq]
          trivial
        · rw [heq]
          exact btFail_inBudget (st := _) hempty
      · have hstep : visitCount re.code re.code.size pc =
            1 + visitCount re.code re.code.size (pc + 1) := by
          rw [visitCount_succ re.code re.code.size pc hpc, if_neg hisacc]
        rcases btStep_loose (hloose pc hpc) hlim hempty with
          ⟨pos', regs, heq⟩ | heq | ⟨regs, heq⟩
        · rw [heq]
          refine ih (pc + 1) pos' _ hempty ⟨a, ?_, hah, hacode⟩ (by omega)
            (by dsimp only [BtSt.visited]; omega)
          rcases Nat.eq_or_lt_of_le hpa with rfl | h
          · exact absurd hacode hisacc
          · omega
        · rw [heq]
          exact btFail_inBudget (st := _) hempty
        · rw [heq]
          trivial

/-- The attempt loop on a budget that covers every starting position it can
still take: no charge it makes is one the caller refused, and what it hands
back still has the delivery in hand. -/
theorem btLoop_inBudget {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start work deliver : Nat}
    (hloose : ∀ q, q < re.code.size → (re.code[q]!).op.loose = true)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept)
    (hwork : visitCount re.code re.code.size 0 ≤ work) :
    ∀ (steps attempt : Nat) (st : BtSt), st.bt.size = 0 → attempt ≤ s.size →
      s.size + 1 - attempt ≤ steps →
      st.m.cost + steps * (re.nregs * regSize + work) + deliver ≤ lim.cost →
      (btLoop re s mo lim start steps attempt st).inBudget ∧
        (btLoop re s mo lim start steps attempt st).state.m.cost + deliver ≤
          lim.cost := by
  obtain ⟨a, ha, hacode⟩ := hreach
  intro steps
  induction steps with
  | zero =>
      intro attempt st hempty hat hsteps hbudget
      omega
  | succ steps ih =>
      intro attempt st hempty hat hsteps hbudget
      rw [Nat.succ_mul] at hbudget
      rw [btLoop_succ]
      split
      · exact absurd hbudget (by omega)
      · have hq := btStep_quiet (re := re) (s := s) (mo := mo) (lim := lim)
          (start := start) (attempt := attempt) hloose
          (lim.cost + 1 - (st.m.cost + re.nregs * regSize)) 0 attempt
          ⟨Array.replicate re.nregs unset32, #[], st.btCap, #[], st.trailCap,
            ⟨st.m.cost + re.nregs * regSize, st.m.mem, st.m.peak⟩,
            st.stackpeak⟩ rfl ⟨a, Nat.zero_le _, ha, hacode⟩
        have hin := btStep_inBudget (re := re) (s := s) (mo := mo) (lim := lim)
          (start := start) (attempt := attempt) hloose
          (lim.cost + 1 - (st.m.cost + re.nregs * regSize)) 0 attempt
          ⟨Array.replicate re.nregs unset32, #[], st.btCap, #[], st.trailCap,
            ⟨st.m.cost + re.nregs * regSize, st.m.mem, st.m.peak⟩,
            st.stackpeak⟩ rfl ⟨a, Nat.zero_le _, ha, hacode⟩ (by omega)
          (by dsimp only; omega)
        have hcost := hq.cost
        dsimp only at hcost
        split
        · rename_i endPos st' hout
          rw [hout] at hcost
          simp only [AttemptOut.state] at hcost
          exact ⟨trivial, by simp only [RunEnd.state]; omega⟩
        · rename_i st' hout
          rw [hout] at hin
          exact absurd hin (by simp [AttemptOut.inBudget])
        · rename_i st' hout
          rw [hout] at hcost hq
          simp only [AttemptOut.state] at hcost hq
          split
          · exact ⟨trivial, by simp only [RunEnd.state]; omega⟩
          · rename_i hanch
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hanch
            split
            · rename_i hskip
              have hlt := Re.skipsAttempt_lt hskip
              exact ih _ st' hq.empty (by omega) (by omega) (by omega)
            · exact ih _ st' hq.empty (by omega) (by omega) (by omega)

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

/-- S-10 for these programs, the backtracking half: a caller whose three
limits sit at or above what the certificate names never sees
ResourceExceeded. Every refusal in the engine is a pre-charge test, and on a
straight-line program the charges are the setup, one reset and one visit per
instruction at each starting position, and the delivery — which is what the
certificate paid for. -/
theorem btRun_inBudget_nest {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hkinds : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .root ∨
      (re.regions[j]!).kind = .group)
    (hreach : ∃ a, a < re.code.size ∧ (re.code[a]!).op = .accept)
    (hcost : cert.cost.val s.size ≤ lim.cost)
    (hmem : cert.mem.val s.size ≤ lim.mem) :
    (btRun re s start mo lim 0 0).outcome ≠ .resourceExceeded := by
  obtain ⟨hwork, hloose⟩ := nest_priced hcert hkinds s.size
  obtain ⟨hdom, -⟩ := certCheck_bt_dom hcert s.size
  obtain ⟨hsetupc, hsetupm⟩ := btRun_setup_ok hcert hcost hmem
  rw [btRun_caps]
  split
  · simp
  rename_i hstart
  split
  · rename_i hguard
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hguard
    omega
  simp only [btReset] at hdom
  have hsteps : (s.size + 1 - start) *
      (re.nregs * regSize + (cert.prices[0]!).work.val s.size) ≤
      (s.size + 1) * (re.nregs * regSize +
        ((cert.prices[0]!).work.val s.size +
          regSize * cert.trail.val s.size)) :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨hin, hleft⟩ := btLoop_inBudget (s := s) (mo := mo) (lim := lim)
    (start := start) (deliver := btDeliver re) hloose hreach hwork
    (s.size + 1 - start) start
    ⟨Array.replicate re.nregs unset32, #[], 0, #[], 0,
      ⟨btSetup re, btSetup re, btSetup re⟩, 0⟩ rfl (by omega) (by omega)
    (by dsimp only; omega)
  split
  · rename_i st' hout
    rw [hout] at hleft
    simp only [RunEnd.state] at hleft
    split
    · omega
    · simp
  · simp
  · rename_i st' hout
    rw [hout] at hin
    exact absurd hin (by simp [RunEnd.inBudget])

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

/-! ## The fork account (BOUNDS.md section 4, once a program forks)

`Quiet` prices a program that never forks, and it prices it by running the
checker's count alongside the VM, instruction for instruction. A split
stops that reading working. An attempt is then no longer a walk from one
instruction to the next but a depth-first traversal of everything the
splits left behind, and the entries the stack is holding are as much a part
of what is still to come as the point the run is standing on.

What replaces it is a potential. A *pricing* gives every program point
three numbers — the visits, the undo entries and the backtrack entries
still to come from it — with a split's numbers covering both of its arms.
What a run still owes is the pricing at the point it stands on plus the
pricing at every resumption point on its stack, and the arrangement is
chosen so that no step ever raises that: a split moves the price of its
second arm off the point that forked and onto the entry it has just pushed,
and a pop moves it back. Every charge a step makes is covered by the drop
it causes, so one entry into the program costs at most what the pricing
says where it started.

`Flow` is the local rule, one program point at a time, and it is closed
under every step the VM can take — which is what makes it an invariant of a
run rather than something assumed about one. It is where the section 3
table appears on this side: a `Save` records an undo entry, a `Split`
pushes a backtrack entry, and nothing else touches either array. The
repetition opcodes are absent on purpose. Their control flow goes
backwards, so a pricing of one has to name the counter as well as the
program point, which is section 4.4 and is not this.

The three accounts travel together because the run mixes them. The trail is
what ties them: a pop charges one register width per undo entry it puts
back, so the cost account has to know what the trail account is holding.
That is why the spend below reads `work + 4 * trail` rather than two
separate numbers, and it is the same reason `charge_call` prices the replay
off the trail claim.

`attemptsWithin_of_flow` reads the whole thing back as `AttemptsWithin`, on
a caller whose memory limit is inside the allocation ceiling. Nothing here
says where a pricing comes from, or that a region's claim dominates one;
that is the checker's half, and it is what the sections below start.
-/

/-- The unit one instruction visit charges, with nothing else moved. -/
def BtSt.tick (st : BtSt) : BtSt :=
  { st with m := { st.m with cost := st.m.cost + 1 } }

/-- What the entries on a backtrack stack still owe, at a price per
resumption point. -/
def owed (f : Nat → Nat) (bt : Array BtEntry) : Nat :=
  bt.foldl (fun n e => n + f e.pc) 0

theorem owed_empty (f : Nat → Nat) : owed f #[] = 0 := by simp [owed]

theorem owed_push (f : Nat → Nat) (bt : Array BtEntry) (e : BtEntry) :
    owed f (bt.push e) = owed f bt + f e.pc := by
  simp [owed]

theorem owed_pop (f : Nat → Nat) {bt : Array BtEntry} (h : bt.size ≠ 0) :
    owed f bt = owed f bt.pop + f bt.back!.pc := by
  rw [← owed_push f bt.pop bt.back!, ← Array.eq_push_pop_back!_of_size_ne_zero h]

/-- Reading a pushed array back below the push. -/
theorem getElem!_push_lt {α : Type _} [Inhabited α] (a : Array α) (x : α) (i : Nat)
    (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h]
  simp [Array.getElem_push, h]

/-- And at the push itself. -/
theorem getElem!_push_self {α : Type _} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp)]
  simp

/-- A popped array reads the same everywhere it still has. -/
theorem getElem!_pop_lt {α : Type _} [Inhabited α] (a : Array α) (i : Nat)
    (h : i < a.pop.size) : a.pop[i]! = a[i]! := by
  rw [getElem!_pos a.pop i h, getElem!_pos a i (by simp at h; omega)]
  simp

/-- Every entry on the stack resumes at a point the pricing covers. -/
def Resumes (Ok : Nat → Prop) (bt : Array BtEntry) : Prop :=
  ∀ i, i < bt.size → Ok (bt[i]!).pc

theorem Resumes.push {Ok : Nat → Prop} {bt : Array BtEntry} {e : BtEntry}
    (h : Resumes Ok bt) (he : Ok e.pc) : Resumes Ok (bt.push e) := by
  intro i hi
  simp only [Array.size_push] at hi
  rcases Nat.lt_or_ge i bt.size with hlt | hge
  · rw [getElem!_push_lt bt e i hlt]
    exact h i hlt
  · have hie : i = bt.size := by omega
    subst hie
    rw [getElem!_push_self]
    exact he

theorem Resumes.pop {Ok : Nat → Prop} {bt : Array BtEntry} (h : Resumes Ok bt) :
    Resumes Ok bt.pop := by
  intro i hi
  rw [getElem!_pop_lt bt i hi]
  exact h i (by simp at hi; omega)

theorem Resumes.back {Ok : Nat → Prop} {bt : Array BtEntry} (h : Resumes Ok bt)
    (hne : bt.size ≠ 0) : Ok bt.back!.pc :=
  h (bt.size - 1) (by omega)

/-- A replay leaves the trail at the mark it was asked for, or where it
already was if that was lower. -/
theorem replayTrail_size :
    ∀ (k : Nat) (t : Array Undo) (r : Array UInt32) (m : Nat), t.size ≤ k →
      (replayTrail t r m).1.size = min t.size m := by
  intro k
  induction k with
  | zero =>
      intro t r m hk
      rw [replayTrail, if_pos (by omega)]
      dsimp only
      omega
  | succ k ih =>
      intro t r m hk
      rw [replayTrail]
      split
      · dsimp only; omega
      · rename_i hlt
        dsimp only
        rw [ih _ _ _ (by simp; omega)]
        simp only [Array.size_pop]
        omega

/-- One visit of an instruction a region holds loose that is neither a
`Save` nor the `Accept`: it charges its unit and either walks on or hands
the failure to the stack. No arm of it touches a register, a capacity or
either array, which is what makes the three accounts below move by exactly
the pricing's own step. -/
theorem btStep_plain {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hloose : (re.code[pc]!).op.loose = true)
    (hsave : (re.code[pc]!).op ≠ .save)
    (hacc : (re.code[pc]!).op ≠ .accept)
    (hlim : ¬ st.m.cost ≥ lim.cost) :
    (∃ pos', btStep re s mo lim start attempt (fuel + 1) pc pos st =
        btStep re s mo lim start attempt fuel (pc + 1) pos' st.tick) ∨
      btStep re s mo lim start attempt (fuel + 1) pc pos st =
        btFail re s mo lim start attempt fuel st.tick := by
  simp only [btStep, BtSt.tick]
  rw [if_neg hlim]
  repeat' split
  all_goals
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr rfl
      | (rw [‹re.code[pc]!.op = Op.save›] at hsave; exact absurd rfl hsave)
      | (rw [‹re.code[pc]!.op = Op.accept›] at hacc; exact absurd rfl hacc)
      | (rw [‹re.code[pc]!.op = Op.split›] at hloose
         exact absurd hloose (by decide))
      | (rw [‹re.code[pc]!.op = Op.jump›] at hloose
         exact absurd hloose (by decide))
      | (rw [‹re.code[pc]!.op = Op.repZero›] at hloose
         exact absurd hloose (by decide))
      | (rw [‹re.code[pc]!.op = Op.repLoop›] at hloose
         exact absurd hloose (by decide))
      | (rw [‹re.code[pc]!.op = Op.repEnter›] at hloose
         exact absurd hloose (by decide))
      | (rw [‹re.code[pc]!.op = Op.repNext›] at hloose
         exact absurd hloose (by decide))

/-- A jump charges its own visit and lands on its target. -/
theorem btStep_jump {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hop : (re.code[pc]!).op = .jump) (hlim : ¬ st.m.cost ≥ lim.cost) :
    btStep re s mo lim start attempt (fuel + 1) pc pos st =
      btStep re s mo lim start attempt fuel (re.code[pc]!).arg pos st.tick := by
  simp only [btStep, BtSt.tick]
  rw [if_neg hlim]
  simp only [hop]

/-- A split whose push the caller's limits refused ends the attempt there,
with the visit charged. -/
theorem btStep_split_none {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hop : (re.code[pc]!).op = .split) (hlim : ¬ st.m.cost ≥ lim.cost)
    (hf : fork st.tick lim (re.code[pc]!).alt pos = none) :
    btStep re s mo lim start attempt (fuel + 1) pc pos st = .exceeded st.tick := by
  simp only [btStep, BtSt.tick]
  rw [if_neg hlim]
  simp only [hop]
  simp only [BtSt.tick] at hf
  rw [hf]

/-- And one that went through remembers its second arm and takes the
first. -/
theorem btStep_split_some {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st st' : BtSt}
    (hop : (re.code[pc]!).op = .split) (hlim : ¬ st.m.cost ≥ lim.cost)
    (hf : fork st.tick lim (re.code[pc]!).alt pos = some st') :
    btStep re s mo lim start attempt (fuel + 1) pc pos st =
      btStep re s mo lim start attempt fuel (re.code[pc]!).arg pos st' := by
  simp only [btStep]
  rw [if_neg hlim]
  simp only [hop]
  simp only [BtSt.tick] at hf
  rw [hf]

/-- The same two readings of a `Save`, whose undo entry the trail has to
have room for. -/
theorem btStep_save_none {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st : BtSt}
    (hop : (re.code[pc]!).op = .save) (hlim : ¬ st.m.cost ≥ lim.cost)
    (hw : writeReg st.tick lim (re.code[pc]!).arg pos.toUInt32 = none) :
    btStep re s mo lim start attempt (fuel + 1) pc pos st = .exceeded st.tick := by
  simp only [btStep, BtSt.tick]
  rw [if_neg hlim]
  simp only [hop]
  simp only [BtSt.tick] at hw
  rw [hw]

theorem btStep_save_some {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt fuel pc pos : Nat} {st st' : BtSt}
    (hop : (re.code[pc]!).op = .save) (hlim : ¬ st.m.cost ≥ lim.cost)
    (hw : writeReg st.tick lim (re.code[pc]!).arg pos.toUInt32 = some st') :
    btStep re s mo lim start attempt (fuel + 1) pc pos st =
      btStep re s mo lim start attempt fuel (pc + 1) pos st' := by
  simp only [btStep]
  rw [if_neg hlim]
  simp only [hop]
  simp only [BtSt.tick] at hw
  rw [hw]

/-- What a fork left on the stack: the entry it pushed, at the trail mark
it was standing on. This is the one thing `fork_within` does not say and
the accounting needs — where the second arm resumes is what the entry is
charged for. -/
theorem fork_pushed {st st' : BtSt} {lim : Limits} {target pos : Nat}
    (h : fork st lim target pos = some st') :
    st'.bt = st.bt.push ⟨target, pos, st.trail.size⟩ := by
  simp only [fork] at h
  split at h
  · exact absurd h (by simp)
  · rename_i mid hp
    simp only [Option.some.injEq] at h
    subst h
    simp only [pushBt] at hp
    split at hp
    · exact absurd hp (by simp)
    · split at hp
      · exact absurd hp (by simp)
      · simp only [Option.some.injEq] at hp
        subst hp
        rfl

/-- A pricing of a program's control flow: at every point a run can reach,
what the rest of the attempt may still visit, record and push.

Every clause is the section 3 table read one step at a time, and the split
clause is the whole of the fork account — the point that forks pays for
both arms, so the entry it pushes carries the second one away with it. The
repetition opcodes have no clause, which refuses them: their control flow
goes backwards and a pricing of one has to name the counter too.

`Ok` is the set of points the pricing covers, and every clause puts each
step's successors back inside it. That closure is what makes this an
invariant of a run and not an assumption about one. -/
def Flow (re : Re) (Ok : Nat → Prop) (W R T : Nat → Nat) : Prop :=
  ∀ pc, Ok pc →
    ((re.code[pc]!).op = .accept ∧ 1 ≤ W pc) ∨
    ((re.code[pc]!).op = .split ∧ Ok (re.code[pc]!).arg ∧ Ok (re.code[pc]!).alt ∧
      1 + W (re.code[pc]!).arg + W (re.code[pc]!).alt ≤ W pc ∧
      R (re.code[pc]!).arg + R (re.code[pc]!).alt ≤ R pc ∧
      1 + T (re.code[pc]!).arg + T (re.code[pc]!).alt ≤ T pc) ∨
    ((re.code[pc]!).op = .jump ∧ Ok (re.code[pc]!).arg ∧
      1 + W (re.code[pc]!).arg ≤ W pc ∧ R (re.code[pc]!).arg ≤ R pc ∧
      T (re.code[pc]!).arg ≤ T pc) ∨
    ((re.code[pc]!).op = .save ∧ Ok (pc + 1) ∧
      1 + W (pc + 1) ≤ W pc ∧ 1 + R (pc + 1) ≤ R pc ∧ T (pc + 1) ≤ T pc) ∨
    ((re.code[pc]!).op.loose = true ∧ (re.code[pc]!).op ≠ .save ∧
      (re.code[pc]!).op ≠ .accept ∧ Ok (pc + 1) ∧
      1 + W (pc + 1) ≤ W pc ∧ R (pc + 1) ≤ R pc ∧ T (pc + 1) ≤ T pc)

/-- A failed path, priced against what the stack is holding. The replay it
charges is one register width per undo entry it puts back, and every one of
those was recorded by a write the trail account already paid for — which is
why the trail is on both sides of the same inequality here and in
`charge_call`. -/
theorem btFail_priced {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt setup stack trail fuel : Nat} {Ok : Nat → Prop}
    {W R T : Nat → Nat}
    (hstep : ∀ (pc pos : Nat) (st : BtSt), Ok pc → Resumes Ok st.bt →
      st.bt.size + T pc + owed T st.bt ≤ stack →
      st.trail.size + R pc + owed R st.bt ≤ trail →
      st.btCap ≤ capacityOf stack → st.trailCap ≤ capacityOf trail →
      st.m.mem = setup + st.reserved →
      Within setup stack trail
        (W pc + owed W st.bt + regSize * (st.trail.size + R pc + owed R st.bt))
        st (btStep re s mo lim start attempt fuel pc pos st).state) :
    ∀ (st : BtSt), Resumes Ok st.bt →
      st.bt.size + owed T st.bt ≤ stack →
      st.trail.size + owed R st.bt ≤ trail →
      st.btCap ≤ capacityOf stack → st.trailCap ≤ capacityOf trail →
      st.m.mem = setup + st.reserved →
      Within setup stack trail
        (owed W st.bt + regSize * (st.trail.size + owed R st.bt))
        st (btFail re s mo lim start attempt fuel st).state := by
  intro st hres hdepth hrec hbt htr hmem
  rw [btFail]
  split
  · refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;>
      (simp only [AttemptOut.state, BtSt.reserved] at hmem ⊢) <;> omega
  · rename_i hne
    dsimp only
    have hpopW := owed_pop W hne
    have hpopR := owed_pop R hne
    have hpopT := owed_pop T hne
    have hsize : st.bt.pop.size = st.bt.size - 1 := by simp
    split
    · refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;>
        (simp only [AttemptOut.state, BtSt.reserved] at hmem ⊢) <;> omega
    · rename_i hroom
      rcases hrt : replayTrail st.trail st.regs st.bt.back!.mark with ⟨t', r'⟩
      dsimp only
      have hts : t'.size = min st.trail.size st.bt.back!.mark := by
        have hall := replayTrail_size st.trail.size st.trail st.regs
          st.bt.back!.mark (Nat.le_refl _)
        rw [hrt] at hall
        exact hall
      have key : ∀ tt : Array Undo, tt.size ≤ min st.trail.size st.bt.back!.mark →
          Within setup stack trail
            (owed W st.bt + regSize * (st.trail.size + owed R st.bt)) st
            (btStep re s mo lim start attempt fuel st.bt.back!.pc st.bt.back!.pos
              ⟨r', st.bt.pop, st.btCap, tt, st.trailCap,
                ⟨st.m.cost + (st.trail.size - st.bt.back!.mark) * regSize,
                  st.m.mem, st.m.peak⟩, st.stackpeak⟩).state := by
        intro tt htt
        have hgo := hstep st.bt.back!.pc st.bt.back!.pos
          ⟨r', st.bt.pop, st.btCap, tt, st.trailCap,
            ⟨st.m.cost + (st.trail.size - st.bt.back!.mark) * regSize,
              st.m.mem, st.m.peak⟩, st.stackpeak⟩
          (hres.back hne) hres.pop (by dsimp only; omega) (by dsimp only; omega)
          (by dsimp only; exact hbt) (by dsimp only; exact htr)
          (by dsimp only [BtSt.reserved] at hmem ⊢; omega)
        refine Within.mono (Within.trans
          (a := (st.trail.size - st.bt.back!.mark) * regSize) ?_ hgo) ?_
        · refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;>
            (dsimp only [BtSt.reserved] at hmem ⊢) <;> omega
        · dsimp only
          simp only [regSize] at *
          omega
      split
      · exact key #[] (by simp)
      · exact key t' (by omega)

set_option maxHeartbeats 1000000 in
/-- One entry into a priced program, priced. The three accounts are carried
together: what the run has left to visit and what its stack still owes,
what the trail is holding and what the rest of the attempt may still
record, and how deep the stack can still go. No step raises any of them,
and every charge a step makes is covered by the drop it causes — which is
the whole of the fork account.

Nothing here is about the region tree. A pricing is a fact about the code,
and where one comes from is the checker's half of BOUNDS.md section 4. -/
theorem btStep_priced {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start attempt setup stack trail : Nat} {Ok : Nat → Prop} {W R T : Nat → Nat}
    (hflow : Flow re Ok W R T) (hlim : lim.mem ≤ ceiling) :
    ∀ (fuel pc pos : Nat) (st : BtSt), Ok pc → Resumes Ok st.bt →
      st.bt.size + T pc + owed T st.bt ≤ stack →
      st.trail.size + R pc + owed R st.bt ≤ trail →
      st.btCap ≤ capacityOf stack → st.trailCap ≤ capacityOf trail →
      st.m.mem = setup + st.reserved →
      Within setup stack trail
        (W pc + owed W st.bt + regSize * (st.trail.size + R pc + owed R st.bt))
        st (btStep re s mo lim start attempt fuel pc pos st).state := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc pos st hok hres hdepth hrec hbt htr hmem
      rw [btStep]
      exact (Within.rfl hbt htr hmem).mono (Nat.zero_le _)
  | succ fuel ih =>
      intro pc pos st hok hres hdepth hrec hbt htr hmem
      by_cases hcost : st.m.cost ≥ lim.cost
      · rw [btStep_exceeded_of_le hcost]
        exact (Within.rfl hbt htr hmem).mono (Nat.zero_le _)
      have hfail := btFail_priced (W := W) (R := R) (T := T) (Ok := Ok) ih
      have htickmem : (BtSt.tick st).m.mem = setup + (BtSt.tick st).reserved := by
        dsimp only [BtSt.tick, BtSt.reserved] at hmem ⊢
        omega
      rcases hflow pc hok with ⟨hop, hW⟩ | ⟨hop, hoka, hokb, hW, hR, hT⟩ |
        ⟨hop, hoka, hW, hR, hT⟩ | ⟨hop, hok1, hW, hR, hT⟩ |
        ⟨hloose, hns, hna, hok1, hW, hR, hT⟩
      -- The Accept: the attempt answers, or hands one last failure back.
      · rcases btStep_accept hop hcost with ⟨regs, heq⟩ | heq
        · rw [heq]
          refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;>
            (dsimp only [AttemptOut.state, BtSt.reserved] at hmem ⊢) <;> omega
        · rw [heq]
          refine Within.mono (Within.trans (Within.charge 1 hbt htr hmem)
            (hfail _ hres (by dsimp only [BtSt.tick]; omega)
              (by dsimp only [BtSt.tick]; omega)
              (by dsimp only [BtSt.tick]; exact hbt)
              (by dsimp only [BtSt.tick]; exact htr)
              (by exact htickmem))) ?_
          dsimp only [BtSt.tick]
          simp only [regSize] at *
          omega
      -- A split: the second arm is remembered, the first one taken.
      · cases hfk : fork (BtSt.tick st) lim (re.code[pc]!).alt pos with
        | none =>
            rw [btStep_split_none hop hcost hfk]
            refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;>
              (dsimp only [AttemptOut.state, BtSt.tick, BtSt.reserved] at hmem ⊢) <;>
              omega
        | some st' =>
            rw [btStep_split_some hop hcost hfk]
            obtain ⟨hwin, hsz, htl, htc⟩ :=
              fork_within (setup := setup) (stack := stack) (trail := trail) hlim
                htickmem hbt htr (by dsimp only [BtSt.tick]; omega) hfk
            have hpush := fork_pushed hfk
            have hoW : owed W st'.bt = owed W st.bt + W (re.code[pc]!).alt := by
              rw [hpush, owed_push]
              rfl
            have hoR : owed R st'.bt = owed R st.bt + R (re.code[pc]!).alt := by
              rw [hpush, owed_push]
              rfl
            have hoT : owed T st'.bt = owed T st.bt + T (re.code[pc]!).alt := by
              rw [hpush, owed_push]
              rfl
            have hts : st'.trail.size = st.trail.size := by rw [htl]; rfl
            have hszv : st'.bt.size = st.bt.size + 1 := by rw [hsz]; rfl
            refine Within.mono (Within.trans (Within.charge 1 hbt htr hmem)
              (Within.trans hwin
                (ih (re.code[pc]!).arg pos st' hoka
                  (hpush ▸ hres.push hokb) (by omega) (by omega)
                  hwin.btRoom hwin.trailRoom hwin.held))) ?_
            simp only [regSize] at *
            omega
      -- A jump: the target, with the visit that got there charged.
      · rw [btStep_jump hop hcost]
        refine Within.mono (Within.trans (Within.charge 1 hbt htr hmem)
          (ih (re.code[pc]!).arg pos (BtSt.tick st) hoka hres
            (by dsimp only [BtSt.tick]; omega) (by dsimp only [BtSt.tick]; omega)
            (by dsimp only [BtSt.tick]; exact hbt)
            (by dsimp only [BtSt.tick]; exact htr) htickmem)) ?_
        dsimp only [BtSt.tick]
        simp only [regSize] at *
        omega
      -- A Save: the undo entry, then on.
      · cases hw : writeReg (BtSt.tick st) lim (re.code[pc]!).arg pos.toUInt32 with
        | none =>
            rw [btStep_save_none hop hcost hw]
            refine ⟨?_, hbt, htr, ?_, ?_, ?_⟩ <;>
              (dsimp only [AttemptOut.state, BtSt.tick, BtSt.reserved] at hmem ⊢) <;>
              omega
        | some st' =>
            rw [btStep_save_some hop hcost hw]
            obtain ⟨hwin, hts, hbteq, hbc, hsp⟩ :=
              writeReg_within (setup := setup) (stack := stack) (trail := trail)
                hlim htickmem hbt htr (by dsimp only [BtSt.tick]; omega) hw
            have htsv : st'.trail.size ≤ st.trail.size + 1 := by
              have hstill : (BtSt.tick st).trail.size = st.trail.size := rfl
              omega
            have hbtv : st'.bt = st.bt := by rw [hbteq]; rfl
            refine Within.mono (Within.trans (Within.charge 1 hbt htr hmem)
              (Within.trans hwin
                (ih (pc + 1) pos st' hok1 (hbtv ▸ hres)
                  (by rw [hbtv]; omega) (by rw [hbtv]; omega)
                  hwin.btRoom hwin.trailRoom hwin.held))) ?_
            rw [hbtv]
            simp only [regSize] at *
            omega
      -- Anything else a region holds loose: one visit, then on or back.
      · rcases btStep_plain hloose hns hna hcost with ⟨pos', heq⟩ | heq
        · rw [heq]
          refine Within.mono (Within.trans (Within.charge 1 hbt htr hmem)
            (ih (pc + 1) pos' (BtSt.tick st) hok1 hres
              (by dsimp only [BtSt.tick]; omega) (by dsimp only [BtSt.tick]; omega)
              (by dsimp only [BtSt.tick]; exact hbt)
              (by dsimp only [BtSt.tick]; exact htr) htickmem)) ?_
          dsimp only [BtSt.tick]
          simp only [regSize] at *
          omega
        · rw [heq]
          refine Within.mono (Within.trans (Within.charge 1 hbt htr hmem)
            (hfail _ hres (by dsimp only [BtSt.tick]; omega)
              (by dsimp only [BtSt.tick]; omega)
              (by dsimp only [BtSt.tick]; exact hbt)
              (by dsimp only [BtSt.tick]; exact htr) htickmem)) ?_
          dsimp only [BtSt.tick]
          simp only [regSize] at *
          omega

/-- A pricing of the program is the section 4 hypothesis: every attempt of
a run stays inside what it says at the entry point. The run starts with an
empty stack and an empty trail, so what it owes at the outset is exactly
the pricing at zero — the composition above does the rest. -/
theorem attemptsWithin_of_flow {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start setup stack trail work : Nat} {Ok : Nat → Prop}
    {W R T : Nat → Nat} (hflow : Flow re Ok W R T) (hlim : lim.mem ≤ ceiling)
    (hstart : Ok 0) (hw : W 0 ≤ work) (hr : R 0 ≤ trail) (ht : T 0 ≤ stack) :
    AttemptsWithin re s mo lim start setup stack trail work := by
  intro attempt fuel st hbt htrail hbtcap htrcap hmem
  have hsz : st.bt.size = 0 := by rw [hbt]; rfl
  have htz : st.trail.size = 0 := by rw [htrail]; rfl
  have howW : owed W st.bt = 0 := by rw [hbt]; exact owed_empty W
  have howR : owed R st.bt = 0 := by rw [hbt]; exact owed_empty R
  have howT : owed T st.bt = 0 := by rw [hbt]; exact owed_empty T
  refine Within.mono (btStep_priced hflow hlim fuel 0 attempt st hstart
    (fun i hi => by omega) (by omega) (by omega) hbtcap htrcap hmem) ?_
  simp only [regSize] at *
  omega

/-! ## A pricing read off the code (BOUNDS.md section 4, checker side)

The fork account asks for a pricing and says nothing about where one comes
from. This is where one comes from: the code itself, one charge per opcode,
with a split's charge covering both of its arms and a jump's its target.
Nothing about the region tree enters yet — a pricing is a fact about the
bytecode, and the tree is what proves a region's claim dominates it.

Reading it off the code needs one thing the bytecode does not carry: that
control only ever moves forward. Straight-line code does, because it moves
by one; an alternation's splits and jumps do, because `shape_alt` pins every
one of them to a later instruction. A repetition does not, and that is the
honest reason the pricing here stops short of section 4.4 — a counted
repetition's `RepNext` jumps back to its own head, so what is still to come
from that point depends on the counter and not on the program point alone.

`scanSpanGo_priced` is the composition, and it is the same walk the earlier
sections read as an opcode inventory, read now as one inequality: the flow
arriving times the pricing at the cursor is covered by what the walk
accumulates plus the flow leaving times the pricing at the end of the range.
A child contributes its own claim and nothing else, which is BOUNDS.md's
"soundness is an induction one step deep" in the form the fork account can
use.
-/

/-- What the rest of an attempt may still cost from a program point, read
straight off the code at one charge per opcode: a split pays for both of its
arms, a jump for its target, an `Accept` for itself alone, and everything
else for the point after it.

`fuel` is the ground still to cover, and `code.size` is always enough of it
on a program whose control flow only ever moves forward. A counted repetition
is where that fails, and it is why this pricing stops short of section 4.4.
An optional item is an ordinary forward split and is not the obstacle. -/
def costAt (code : Array Inst) (unit : Inst → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, pc =>
      if pc ≥ code.size then 0
      else
        match (code[pc]!).op with
        | .accept => unit (code[pc]!)
        | .split =>
            unit (code[pc]!) + costAt code unit fuel (code[pc]!).arg
              + costAt code unit fuel (code[pc]!).alt
        | .jump => unit (code[pc]!) + costAt code unit fuel (code[pc]!).arg
        | _ => unit (code[pc]!) + costAt code unit fuel (pc + 1)

/-- Control at this point only ever moves forward. Straight-line code moves
forward because it moves by one; what an alternation's splits and jumps do
is `shape_alt`'s business, and a repetition is exactly where this is
false. -/
def Inst.forward (code : Array Inst) (pc : Nat) : Prop :=
  ((code[pc]!).op = .split → pc < (code[pc]!).arg ∧ pc < (code[pc]!).alt) ∧
    ((code[pc]!).op = .jump → pc < (code[pc]!).arg)

/-- More fuel than the ground left changes nothing. -/
theorem costAt_stable {code : Array Inst} {unit : Inst → Nat}
    (hfwd : ∀ pc, pc < code.size → Inst.forward code pc) :
    ∀ (f pc : Nat), code.size - pc ≤ f →
      costAt code unit f pc = costAt code unit (f + 1) pc := by
  intro f
  induction f with
  | zero =>
      intro pc hk
      rw [costAt, costAt, if_pos (by omega)]
  | succ f ih =>
      intro pc hk
      by_cases hpc : pc ≥ code.size
      · rw [costAt, costAt, if_pos hpc, if_pos hpc]
      · rw [costAt, costAt, if_neg hpc, if_neg hpc]
        obtain ⟨hsp, hjp⟩ := hfwd pc (by omega)
        split
        · rfl
        · rename_i hop
          rw [← ih _ (by have := (hsp hop).1; omega), ← ih _ (by have := (hsp hop).2; omega)]
        · rename_i hop
          rw [← ih _ (by have := hjp hop; omega)]
        · rw [← ih (pc + 1) (by omega)]

/-- So any two sufficient fuels agree. -/
theorem costAt_const {code : Array Inst} {unit : Inst → Nat}
    (hfwd : ∀ pc, pc < code.size → Inst.forward code pc) :
    ∀ (f g pc : Nat), code.size - pc ≤ f → f ≤ g →
      costAt code unit f pc = costAt code unit g pc := by
  intro f g pc hf hfg
  induction g with
  | zero => have : f = 0 := by omega
            rw [this]
  | succ g ih =>
      rcases Nat.eq_or_lt_of_le hfg with rfl | hlt
      · rfl
      · rw [ih (by omega), costAt_stable hfwd g pc (by omega)]



/-- The pricing itself, run on the whole program's worth of fuel. -/
def flowCost (code : Array Inst) (unit : Inst → Nat) (pc : Nat) : Nat :=
  costAt code unit code.size pc

/-- Past the end of the program there is nothing left to charge — which is
what makes a program that can walk off its own end unpriceable, since the
clauses below would then ask a natural number to keep decreasing. -/
theorem flowCost_out {code : Array Inst} {unit : Inst → Nat} {pc : Nat}
    (h : code.size ≤ pc) : flowCost code unit pc = 0 := by
  unfold flowCost
  cases hsz : code.size with
  | zero => rw [costAt]
  | succ f => rw [costAt, if_pos (by omega)]

/-- One step of the pricing, with the fuel taken out. -/
theorem flowCost_unfold {code : Array Inst} {unit : Inst → Nat} {pc : Nat}
    (hfwd : ∀ q, q < code.size → Inst.forward code q) (hpc : pc < code.size) :
    flowCost code unit pc =
      match (code[pc]!).op with
      | .accept => unit (code[pc]!)
      | .split =>
          unit (code[pc]!) + flowCost code unit (code[pc]!).arg
            + flowCost code unit (code[pc]!).alt
      | .jump => unit (code[pc]!) + flowCost code unit (code[pc]!).arg
      | _ => unit (code[pc]!) + flowCost code unit (pc + 1) := by
  obtain ⟨f, hf⟩ : ∃ f, code.size = f + 1 := ⟨code.size - 1, by omega⟩
  obtain ⟨hsp, hjp⟩ := hfwd pc hpc
  unfold flowCost
  have hL : costAt code unit code.size pc = costAt code unit (f + 1) pc := by
    rw [hf]
  rw [hL, costAt, if_neg (by omega)]
  split
  · rfl
  · rename_i hop
    rw [costAt_const hfwd f code.size _ (by have := (hsp hop).1; omega) (by omega),
      costAt_const hfwd f code.size _ (by have := (hsp hop).2; omega) (by omega)]
  · rename_i hop
    rw [costAt_const hfwd f code.size _ (by have := hjp hop; omega) (by omega)]
  · rw [costAt_const hfwd f code.size (pc + 1) (by omega) (by omega)]



/-- The four readings of that step, one per opcode shape. -/
theorem flowCost_accept {code : Array Inst} {unit : Inst → Nat} {pc : Nat}
    (hfwd : ∀ q, q < code.size → Inst.forward code q) (hpc : pc < code.size)
    (hop : (code[pc]!).op = .accept) :
    flowCost code unit pc = unit (code[pc]!) := by
  rw [flowCost_unfold hfwd hpc, hop]

theorem flowCost_split {code : Array Inst} {unit : Inst → Nat} {pc : Nat}
    (hfwd : ∀ q, q < code.size → Inst.forward code q) (hpc : pc < code.size)
    (hop : (code[pc]!).op = .split) :
    flowCost code unit pc =
      unit (code[pc]!) + flowCost code unit (code[pc]!).arg
        + flowCost code unit (code[pc]!).alt := by
  rw [flowCost_unfold hfwd hpc, hop]

theorem flowCost_jump {code : Array Inst} {unit : Inst → Nat} {pc : Nat}
    (hfwd : ∀ q, q < code.size → Inst.forward code q) (hpc : pc < code.size)
    (hop : (code[pc]!).op = .jump) :
    flowCost code unit pc =
      unit (code[pc]!) + flowCost code unit (code[pc]!).arg := by
  rw [flowCost_unfold hfwd hpc, hop]

theorem flowCost_step {code : Array Inst} {unit : Inst → Nat} {pc : Nat}
    (hfwd : ∀ q, q < code.size → Inst.forward code q) (hpc : pc < code.size)
    (h1 : (code[pc]!).op ≠ .accept) (h2 : (code[pc]!).op ≠ .split)
    (h3 : (code[pc]!).op ≠ .jump) :
    flowCost code unit pc = unit (code[pc]!) + flowCost code unit (pc + 1) := by
  rw [flowCost_unfold hfwd hpc]
  split
  · exact absurd ‹(code[pc]!).op = Op.accept› h1
  · exact absurd ‹(code[pc]!).op = Op.split› h2
  · exact absurd ‹(code[pc]!).op = Op.jump› h3
  · rfl

/-- The three charges of the BOUNDS.md section 3 table, as units the pricing
above weighs a program point with: every visit, an undo entry at each
`Save`, and a backtrack entry at each `Split`. -/
def unitVisit (_ : Inst) : Nat := 1
def unitRecord (i : Inst) : Nat := if i.op = .save then 1 else 0
def unitPush (i : Inst) : Nat := if i.op = .split then 1 else 0

theorem unitRecord_save {i : Inst} (h : i.op = .save) : unitRecord i = 1 := by
  simp [unitRecord, h]

theorem unitRecord_ne {i : Inst} (h : i.op ≠ .save) : unitRecord i = 0 := by
  simp [unitRecord, h]

theorem unitPush_split {i : Inst} (h : i.op = .split) : unitPush i = 1 := by
  simp [unitPush, h]

theorem unitPush_ne {i : Inst} (h : i.op ≠ .split) : unitPush i = 0 := by
  simp [unitPush, h]

/-- A program whose control flow moves forward, whose points are closed
under stepping and which holds no repetition opcode has a pricing, and it is
the one read off the code. Those three hypotheses are what an assembly over
the region tree has to produce; none of them is read off `cert_shape`
here. -/
theorem flow_of_forward {re : Re} {Ok : Nat → Prop}
    (hfwd : ∀ q, q < re.code.size → Inst.forward re.code q)
    (hin : ∀ pc, Ok pc → pc < re.code.size)
    (hkind : ∀ pc, Ok pc → (re.code[pc]!).op.loose = true ∨
      (re.code[pc]!).op = .split ∨ (re.code[pc]!).op = .jump)
    (hnext : ∀ pc, Ok pc →
      ((re.code[pc]!).op = .split → Ok (re.code[pc]!).arg ∧ Ok (re.code[pc]!).alt) ∧
      ((re.code[pc]!).op = .jump → Ok (re.code[pc]!).arg) ∧
      ((re.code[pc]!).op ≠ .split → (re.code[pc]!).op ≠ .jump →
        (re.code[pc]!).op ≠ .accept → Ok (pc + 1))) :
    Flow re Ok (flowCost re.code unitVisit) (flowCost re.code unitRecord)
      (flowCost re.code unitPush) := by
  intro pc hok
  have hpc := hin pc hok
  obtain ⟨hsp, hjp, hnx⟩ := hnext pc hok
  by_cases hacc : (re.code[pc]!).op = .accept
  · refine Or.inl ⟨hacc, ?_⟩
    rw [flowCost_accept hfwd hpc hacc]
    exact Nat.le_refl _
  by_cases hspl : (re.code[pc]!).op = .split
  · have hne : (re.code[pc]!).op ≠ .save := by rw [hspl]; decide
    refine Or.inr (Or.inl ⟨hspl, (hsp hspl).1, (hsp hspl).2, ?_, ?_, ?_⟩)
    · rw [flowCost_split hfwd hpc hspl, unitVisit]
      omega
    · rw [flowCost_split hfwd hpc hspl, unitRecord_ne hne]
      omega
    · rw [flowCost_split hfwd hpc hspl, unitPush_split hspl]
      omega
  by_cases hjmp : (re.code[pc]!).op = .jump
  · have hne : (re.code[pc]!).op ≠ .save := by rw [hjmp]; decide
    have hnp : (re.code[pc]!).op ≠ .split := hspl
    refine Or.inr (Or.inr (Or.inl ⟨hjmp, hjp hjmp, ?_, ?_, ?_⟩))
    · rw [flowCost_jump hfwd hpc hjmp, unitVisit]
      omega
    · rw [flowCost_jump hfwd hpc hjmp, unitRecord_ne hne]
      omega
    · rw [flowCost_jump hfwd hpc hjmp, unitPush_ne hnp]
      omega
  by_cases hsav : (re.code[pc]!).op = .save
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hsav, hnx hspl hjmp hacc, ?_, ?_, ?_⟩)))
    · rw [flowCost_step hfwd hpc hacc hspl hjmp, unitVisit]
      omega
    · rw [flowCost_step hfwd hpc hacc hspl hjmp, unitRecord_save hsav]
      omega
    · rw [flowCost_step hfwd hpc hacc hspl hjmp, unitPush_ne hspl]
      omega
  · refine Or.inr (Or.inr (Or.inr (Or.inr
      ⟨?_, hsav, hacc, hnx hspl hjmp hacc, ?_, ?_, ?_⟩)))
    · rcases hkind pc hok with h | h | h
      · exact h
      · exact absurd h hspl
      · exact absurd h hjmp
    · rw [flowCost_step hfwd hpc hacc hspl hjmp, unitVisit]
      omega
    · rw [flowCost_step hfwd hpc hacc hspl hjmp, unitRecord_ne hsav]
      omega
    · rw [flowCost_step hfwd hpc hacc hspl hjmp, unitPush_ne hspl]
      omega



set_option maxHeartbeats 1000000 in
/-- BOUNDS.md section 4.1 against the pricing: walking a straight-line range
left to right, the flow arriving times what the code-level pricing says at
the cursor is covered by what the walk accumulates plus the flow leaving
times what the pricing says at the end.

That single inequality is the composition. At a child it turns into the
child's own claim — `hkid` is the induction one step deep, in exactly the
form the region below has to supply — and at an instruction it turns into
the section 3 table, which `hcode` states as three inequalities on the
pricing itself. An `Accept` is the one place the flow is dropped rather than
carried, and the pricing has to agree: a match ends the attempt, so nothing
downstream is reached by way of it and the point costs one visit and
nothing else.

Nothing here mentions the run, and neither premise is discharged here:
`hcode` is what the recurrences of `costAt` give at every point of the
range, and `hkid` is the same conclusion at the region below. What comes out
is that conclusion for this region — the step of a tree induction, not the
induction. -/
theorem scanSpanGo_priced {code : Array Inst} {regions : Array Region}
    {prices : Array Price} {sibs : Array Nat} {hi n : Nat} {W R T : Nat → Nat}
    (hcode : ∀ pc, pc < hi → (code[pc]!).op ≠ .split → (code[pc]!).op ≠ .jump →
      (W pc ≤ 1 + W (pc + 1) ∧ R pc ≤ 1 + R (pc + 1) ∧ T pc ≤ T (pc + 1)) ∧
      ((code[pc]!).op ≠ .save → R pc ≤ R (pc + 1)) ∧
      ((code[pc]!).op = .accept → W pc ≤ 1 ∧ R pc = 0 ∧ T pc = 0))
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      (regions[c]!).lo < (regions[c]!).hi →
      W (regions[c]!).lo ≤ (prices[c]!).work.val n
          + (prices[c]!).outs.val n * W (regions[c]!).hi ∧
        R (regions[c]!).lo ≤ (prices[c]!).trail.val n
          + (prices[c]!).outs.val n * R (regions[c]!).hi ∧
        T (regions[c]!).lo ≤ (prices[c]!).stack.val n
          + (prices[c]!).outs.val n * T (regions[c]!).hi ∧
        (regions[c]!).hi ≤ hi) :
    ∀ (k pc cursor : Nat), P cursor → hi - pc ≤ k → pc ≤ hi →
      ∀ (acc acc' : Acc) (over over' : Bool),
      scanSpanGo code regions prices sibs hi pc cursor acc over =
        (.crOk, acc', over') → over' = false →
      over = false ∧
        acc.work.val n + acc.flow.val n * W pc ≤
          acc'.work.val n + acc'.flow.val n * W hi ∧
        acc.trail.val n + acc.flow.val n * R pc ≤
          acc'.trail.val n + acc'.flow.val n * R hi ∧
        acc.stack.val n + acc.flow.val n * T pc ≤
          acc'.stack.val n + acc'.flow.val n * T hi := by
  intro k
  induction k with
  | zero =>
      intro pc cursor hP hk hle acc acc' over over' h hover
      have hpe : pc = hi := by omega
      subst hpe
      rw [scanSpanGo, dif_neg (by omega)] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, hacc, hov⟩ := h
      subst hacc
      subst hov
      exact ⟨hover, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | succ k ih =>
      intro pc cursor hP hk hle acc acc' over over' h hover
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
          obtain ⟨hcw, hcr, hct, hchi⟩ := hkid cursor hP hcond.1 (by omega)
          obtain ⟨hov, hw, hr, ht⟩ :=
            ih (regions[cursor]!).hi (sibs[cursor]!) (hsib cursor hP hcond.1)
              (by omega) hchi _ _ _ _ h hover
          dsimp only at hw hr ht
          have f6 := polyMul_snd hov
          have f5 := polyAdd_snd f6
          have f4 := polyMul_snd f5
          have f3 := polyAdd_snd f4
          have f2 := polyMul_snd f3
          have f1 := polyAdd_snd f2
          have vcw := polyMul_eq f1 n
          have vw := polyAdd_le f2 n
          have vcs := polyMul_eq f3 n
          have vs := polyAdd_le f4 n
          have vct := polyMul_eq f5 n
          have vt := polyAdd_le f6 n
          have von := polyMul_eq hov n
          rw [von] at hw hr ht
          refine ⟨polyMul_snd f1, ?_, ?_, ?_⟩
          · have hm : acc.flow.val n * W pc ≤
                acc.flow.val n * (prices[cursor]!).work.val n
                  + acc.flow.val n * (prices[cursor]!).outs.val n *
                    W (regions[cursor]!).hi := by
              have h1 : acc.flow.val n * W pc ≤ acc.flow.val n *
                  ((prices[cursor]!).work.val n + (prices[cursor]!).outs.val n *
                    W (regions[cursor]!).hi) :=
                Nat.mul_le_mul_left _ (by rw [← hcond.2]; exact hcw)
              rw [Nat.mul_add, ← Nat.mul_assoc] at h1
              exact h1
            omega
          · have hm : acc.flow.val n * R pc ≤
                acc.flow.val n * (prices[cursor]!).trail.val n
                  + acc.flow.val n * (prices[cursor]!).outs.val n *
                    R (regions[cursor]!).hi := by
              have h1 : acc.flow.val n * R pc ≤ acc.flow.val n *
                  ((prices[cursor]!).trail.val n + (prices[cursor]!).outs.val n *
                    R (regions[cursor]!).hi) :=
                Nat.mul_le_mul_left _ (by rw [← hcond.2]; exact hcr)
              rw [Nat.mul_add, ← Nat.mul_assoc] at h1
              exact h1
            omega
          · have hm : acc.flow.val n * T pc ≤
                acc.flow.val n * (prices[cursor]!).stack.val n
                  + acc.flow.val n * (prices[cursor]!).outs.val n *
                    T (regions[cursor]!).hi := by
              have h1 : acc.flow.val n * T pc ≤ acc.flow.val n *
                  ((prices[cursor]!).stack.val n + (prices[cursor]!).outs.val n *
                    T (regions[cursor]!).hi) :=
                Nat.mul_le_mul_left _ (by rw [← hcond.2]; exact hct)
              rw [Nat.mul_add, ← Nat.mul_assoc] at h1
              exact h1
            omega
        · -- an instruction this range holds itself
          rename_i hcond
          dsimp only at h
          by_cases hacc : (code[pc]!).op = .accept
          · obtain ⟨⟨hw1, hr1, ht1⟩, hrns, haccv⟩ :=
              hcode pc hpc (by rw [hacc]; decide) (by rw [hacc]; decide)
            simp only [hacc] at h
            obtain ⟨hW0, hR0, hT0⟩ := haccv hacc
            obtain ⟨hov, hw, hr, ht⟩ :=
              ih (pc + 1) cursor hP (by omega) (by omega) _ _ _ _ h hover
            dsimp only at hw hr ht
            have hvis := polyAdd_le hov n
            simp only [Poly.val_zero, Nat.zero_mul] at hw hr ht
            refine ⟨polyAdd_snd hov, ?_, ?_, ?_⟩
            · have hm : acc.flow.val n * W pc ≤ acc.flow.val n * 1 :=
                Nat.mul_le_mul_left _ hW0
              rw [Nat.mul_one] at hm
              omega
            · have hm : acc.flow.val n * R pc = 0 := by rw [hR0, Nat.mul_zero]
              omega
            · have hm : acc.flow.val n * T pc = 0 := by rw [hT0, Nat.mul_zero]
              omega
          by_cases hsav : (code[pc]!).op = .save
          · obtain ⟨⟨hw1, hr1, ht1⟩, hrns, haccv⟩ :=
              hcode pc hpc (by rw [hsav]; decide) (by rw [hsav]; decide)
            simp only [hsav] at h
            obtain ⟨hov, hw, hr, ht⟩ :=
              ih (pc + 1) cursor hP (by omega) (by omega) _ _ _ _ h hover
            dsimp only at hw hr ht
            have f1 := polyAdd_snd hov
            have hvisw := polyAdd_le f1 n
            have hvist := polyAdd_le hov n
            refine ⟨polyAdd_snd f1, ?_, ?_, ?_⟩
            · have hm : acc.flow.val n * W pc ≤ acc.flow.val n * (1 + W (pc + 1)) :=
                Nat.mul_le_mul_left _ hw1
              rw [Nat.mul_add, Nat.mul_one] at hm
              omega
            · have hm : acc.flow.val n * R pc ≤ acc.flow.val n * (1 + R (pc + 1)) :=
                Nat.mul_le_mul_left _ hr1
              rw [Nat.mul_add, Nat.mul_one] at hm
              omega
            · have hm : acc.flow.val n * T pc ≤ acc.flow.val n * T (pc + 1) :=
                Nat.mul_le_mul_left _ ht1
              omega
          · split at h
            all_goals rename_i hop
            all_goals
              first
                | (simp only [Prod.mk.injEq] at h
                   exact absurd h.1 (by decide))
                | exact absurd hop hacc
                | exact absurd hop hsav
                | (obtain ⟨⟨hw1, hr1, ht1⟩, hrns, haccv⟩ :=
                     hcode pc hpc (by rw [hop]; decide) (by rw [hop]; decide)
                   obtain ⟨hov, hw, hr, ht⟩ :=
                     ih (pc + 1) cursor hP (by omega) (by omega) _ _ _ _ h hover
                   dsimp only at hw hr ht
                   have hvis := polyAdd_le hov n
                   have hrn := hrns hsav
                   refine ⟨polyAdd_snd hov, ?_, ?_, ?_⟩
                   · have hm : acc.flow.val n * W pc ≤
                         acc.flow.val n * (1 + W (pc + 1)) :=
                       Nat.mul_le_mul_left _ hw1
                     rw [Nat.mul_add, Nat.mul_one] at hm
                     omega
                   · have hm : acc.flow.val n * R pc ≤ acc.flow.val n * R (pc + 1) :=
                       Nat.mul_le_mul_left _ hrn
                     omega
                   · have hm : acc.flow.val n * T pc ≤ acc.flow.val n * T (pc + 1) :=
                       Nat.mul_le_mul_left _ ht1
                     omega)
      · have hpe : pc = hi := by omega
        subst hpe
        rw [scanSpanGo, dif_neg hpc] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, hacc, hov⟩ := h
        subst hacc
        subst hov
        exact ⟨hover, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-! ## Alternation, priced (BOUNDS.md section 4.2)

An alternation is the first construct whose region does not walk its own
code. `scan_alt` reads the branches off the child list and prices them, and
`shape_alt` is what ties that list back to the bytecode: for every branch
but the last there is a split whose fall-through arm is the branch's first
instruction and whose second arm is the instruction after the branch's
closing jump, and that jump goes to the end of the alternation. The two
walks therefore have to be run in step, which is what the pricing below
does.

What comes out is the section 4.2 equations, one inequality per account. The
`k-1` in `work` and in `stack` is the splits, one per branch but the last;
the second sum in `work` is the closing jumps; and `outs` is the sum over
branches, because the flow leaving each of them arrives at the same place.
The rules are at their most conservative here on purpose — nothing knows
that two branches cannot both match the same byte — and that shows up as a
sum where a first-byte disjointness rule would give a maximum.

What is here is the chain induction rather than an alternation priced on its
own. Its conclusion is the same one a straight-line region's walk produces,
which is what lets an `RkAlt` region slot into the tree induction below
beside the others.
-/

/-- One step of `shape_alt`'s walk, read as the code layout it settled. A
branch with another after it has a split before it and a jump after it, both
pinned to the branch's own range and to the end of the alternation; the last
branch simply runs to that end. Everything the pricing below needs about the
bytecode is here, and nothing else is. -/
theorem shapeAltGo_step {code : Array Inst} {regions : Array Region}
    {sibs : Array Nat} {hi fuel p c k : Nat} (hne : c ≠ none32)
    (h : shapeAltGo code regions sibs hi (fuel + 1) p c k = .crOk) :
    (sibs[c]! ≠ none32 ∧ p < hi ∧ (code[p]!).op = .split ∧
        (code[p]!).arg = p + 1 ∧ (regions[c]!).lo = p + 1 ∧
        (regions[c]!).hi < hi ∧ (code[(regions[c]!).hi]!).op = .jump ∧
        (code[(regions[c]!).hi]!).arg = hi ∧
        (code[p]!).alt = (regions[c]!).hi + 1 ∧
        shapeAltGo code regions sibs hi fuel ((regions[c]!).hi + 1) (sibs[c]!)
          (k + 1) = .crOk) ∨
      (sibs[c]! = none32 ∧ (regions[c]!).lo = p ∧ (regions[c]!).hi = hi ∧
        shapeAltGo code regions sibs hi fuel p (sibs[c]!) (k + 1) = .crOk) := by
  rw [shapeAltGo, if_neg (show ¬((c == none32) = true) by simp [hne])] at h
  dsimp only at h
  by_cases hkind : (regions[c]!).kind ≠ .branch
  · rw [if_pos hkind] at h
    exact absurd h (by decide)
  rw [if_neg hkind] at h
  by_cases hnxt : sibs[c]! ≠ none32
  · rw [if_pos hnxt] at h
    by_cases hph : p ≥ hi
    · rw [if_pos hph] at h
      exact absurd h (by decide)
    rw [if_neg hph] at h
    by_cases hfork : (code[p]!).op ≠ .split
    · rw [if_pos hfork] at h
      exact absurd h (by decide)
    rw [if_neg hfork] at h
    by_cases harg : (code[p]!).arg ≠ p + 1
    · rw [if_pos harg] at h
      exact absurd h (by decide)
    rw [if_neg harg] at h
    by_cases hlo : (regions[c]!).lo ≠ p + 1
    · rw [if_pos hlo] at h
      exact absurd h (by decide)
    rw [if_neg hlo] at h
    by_cases hstop : (regions[c]!).hi ≥ hi
    · rw [if_pos hstop] at h
      exact absurd h (by decide)
    rw [if_neg hstop] at h
    by_cases hleave : (code[(regions[c]!).hi]!).op ≠ .jump ∨
        (code[(regions[c]!).hi]!).arg ≠ hi
    · rw [if_pos hleave] at h
      exact absurd h (by decide)
    rw [if_neg hleave] at h
    by_cases halt : (code[p]!).alt ≠ (regions[c]!).hi + 1
    · rw [if_pos halt] at h
      exact absurd h (by decide)
    rw [if_neg halt] at h
    simp only [not_or, ne_eq, Decidable.not_not] at hfork harg hlo hleave halt
    exact Or.inl ⟨hnxt, by omega, hfork, harg, hlo, by omega, hleave.1, hleave.2,
      halt, h⟩
  · rw [if_neg hnxt] at h
    by_cases hends : (regions[c]!).lo ≠ p ∨ (regions[c]!).hi ≠ hi
    · rw [if_pos hends] at h
      exact absurd h (by decide)
    rw [if_neg hends] at h
    simp only [not_or, ne_eq, Decidable.not_not] at hnxt hends
    exact Or.inr ⟨hnxt, hends.1, hends.2, h⟩



/-- The chain walk stops at the sentinel, whatever fuel is left. -/
theorem scanAltGo_none (prices : Array Price) (sibs : Array Nat) (fuel : Nat)
    (acc : Acc) (over : Bool) :
    scanAltGo prices sibs fuel none32 acc over = (.crOk, acc, over) := by
  cases fuel with
  | zero => rw [scanAltGo]
  | succ f => rw [scanAltGo, if_pos (by simp)]

set_option maxHeartbeats 1000000 in
/-- BOUNDS.md section 4.2 against the pricing, with `scan_alt` and
`shape_alt` walked in step.

The invariant is the one shape that makes a chain of splits compose: the
flow accumulated so far, weighed at the end of the alternation, plus what
the pricing still says at the split about to be entered. A branch with
another after it turns that into a split, the branch, its closing jump and
the rest of the chain — and the jump is where a branch's `outs` is charged a
second time, once per way that branch found to succeed. The last branch
turns it into the branch alone, since it runs to the end of the region and
needs no jump to get there.

Nothing asks a branch to cover an instruction. `a|` has a second arm that
compiles to nothing, and the record of it is still on the child list because
the shape check needs a branch to line up against the split.

The claim is guarded by the cursor not being the sentinel, which is what
makes it a step of the chain rather than a statement about one call: at the
sentinel there is no split left to enter and nothing to say. -/
theorem scanAltGo_priced {code : Array Inst} {regions : Array Region}
    {prices : Array Price} {sibs : Array Nat} {hi n : Nat} {W R T : Nat → Nat}
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hsplit : ∀ p, (code[p]!).op = .split →
      W p ≤ 1 + W (code[p]!).arg + W (code[p]!).alt ∧
      R p ≤ R (code[p]!).arg + R (code[p]!).alt ∧
      T p ≤ 1 + T (code[p]!).arg + T (code[p]!).alt)
    (hjump : ∀ p, (code[p]!).op = .jump →
      W p ≤ 1 + W (code[p]!).arg ∧ R p ≤ R (code[p]!).arg ∧
      T p ≤ T (code[p]!).arg)
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      W (regions[c]!).lo ≤ (prices[c]!).work.val n
          + (prices[c]!).outs.val n * W (regions[c]!).hi ∧
        R (regions[c]!).lo ≤ (prices[c]!).trail.val n
          + (prices[c]!).outs.val n * R (regions[c]!).hi ∧
        T (regions[c]!).lo ≤ (prices[c]!).stack.val n
          + (prices[c]!).outs.val n * T (regions[c]!).hi) :
    ∀ (fuel p c k : Nat) (acc acc' : Acc) (over over' : Bool), P c →
      shapeAltGo code regions sibs hi fuel p c k = .crOk →
      scanAltGo prices sibs fuel c acc over = (.crOk, acc', over') →
      over' = false →
      over = false ∧ (c ≠ none32 →
        acc.work.val n + acc.flow.val n * W hi + W p ≤
          acc'.work.val n + acc'.flow.val n * W hi ∧
        acc.trail.val n + acc.flow.val n * R hi + R p ≤
          acc'.trail.val n + acc'.flow.val n * R hi ∧
        acc.stack.val n + acc.flow.val n * T hi + T p ≤
          acc'.stack.val n + acc'.flow.val n * T hi) := by
  intro fuel
  induction fuel with
  | zero =>
      intro p c k acc acc' over over' hP hshape hscan hover
      rw [shapeAltGo] at hshape
      split at hshape
      · exact absurd hshape (by decide)
      rename_i hnone
      simp only [ne_eq, Decidable.not_not] at hnone
      rw [scanAltGo] at hscan
      simp only [Prod.mk.injEq] at hscan
      obtain ⟨-, ha, ho⟩ := hscan
      subst ha
      subst ho
      exact ⟨hover, fun hc => absurd hnone hc⟩
  | succ fuel ih =>
      intro p c k acc acc' over over' hP hshape hscan hover
      by_cases hne : c = none32
      · subst hne
        rw [scanAltGo_none] at hscan
        simp only [Prod.mk.injEq] at hscan
        obtain ⟨-, ha, ho⟩ := hscan
        subst ha
        subst ho
        exact ⟨hover, fun hc => absurd rfl hc⟩
      obtain ⟨hkw, hkr, hkt⟩ := hkid c hP hne
      rw [scanAltGo, if_neg (show ¬((c == none32) = true) by simp [hne])] at hscan
      dsimp only at hscan
      rcases shapeAltGo_step hne hshape with
        ⟨hnxt, hph, hforkop, harg, hlo, hstop, hleaveop, hleavearg, halt, hrec⟩ |
        ⟨hnxt, hlo, hhi, hrec⟩
      · -- a branch with another after it: a split before it, a jump after
        rw [if_pos (show (sibs[c]! != none32) = true by simp [hnxt])] at hscan
        dsimp only at hscan
        obtain ⟨hov, hrest⟩ :=
          ih ((regions[c]!).hi + 1) (sibs[c]!) (k + 1) _ _ _ _
            (hsib c hP hne) hrec hscan hover
        obtain ⟨hw, hr, ht⟩ := hrest hnxt
        dsimp only at hw hr ht
        have f6 := polyAdd_snd hov
        have f5 := polyAdd_snd f6
        have f4 := polyAdd_snd f5
        have f3 := polyAdd_snd f4
        have f2 := polyAdd_snd f3
        have f1 := polyAdd_snd f2
        have v1 := polyAdd_le f1 n
        have v2 := polyAdd_le f2 n
        have v3 := polyAdd_le f3 n
        have v4 := polyAdd_le f4 n
        have v5 := polyAdd_le f5 n
        have v6 := polyAdd_le f6 n
        have v7 := polyAdd_le hov n
        rw [Poly.val_const] at v1 v3
        obtain ⟨hsW, hsR, hsT⟩ := hsplit p hforkop
        obtain ⟨hjW, hjR, hjT⟩ := hjump (regions[c]!).hi hleaveop
        rw [harg, halt] at hsW hsR hsT
        rw [hleavearg] at hjW hjR hjT
        rw [hlo] at hkw hkr hkt
        refine ⟨polyAdd_snd f1, fun _ => ⟨?_, ?_, ?_⟩⟩
        · have m1 : (prices[c]!).outs.val n * W (regions[c]!).hi ≤
              (prices[c]!).outs.val n * (1 + W hi) := Nat.mul_le_mul_left _ hjW
          rw [Nat.mul_add, Nat.mul_one] at m1
          have m2 : (acc.flow.val n + (prices[c]!).outs.val n) * W hi ≤
              (polyAdd acc.flow (prices[c]!).outs
                (polyAdd acc.trail (prices[c]!).trail _).2).1.val n * W hi :=
            Nat.mul_le_mul_right _ v7
          rw [Nat.add_mul] at m2
          omega
        · have m1 : (prices[c]!).outs.val n * R (regions[c]!).hi ≤
              (prices[c]!).outs.val n * R hi := Nat.mul_le_mul_left _ hjR
          have m2 : (acc.flow.val n + (prices[c]!).outs.val n) * R hi ≤
              (polyAdd acc.flow (prices[c]!).outs
                (polyAdd acc.trail (prices[c]!).trail _).2).1.val n * R hi :=
            Nat.mul_le_mul_right _ v7
          rw [Nat.add_mul] at m2
          omega
        · have m1 : (prices[c]!).outs.val n * T (regions[c]!).hi ≤
              (prices[c]!).outs.val n * T hi := Nat.mul_le_mul_left _ hjT
          have m2 : (acc.flow.val n + (prices[c]!).outs.val n) * T hi ≤
              (polyAdd acc.flow (prices[c]!).outs
                (polyAdd acc.trail (prices[c]!).trail _).2).1.val n * T hi :=
            Nat.mul_le_mul_right _ v7
          rw [Nat.add_mul] at m2
          omega
      · -- the last branch: it runs to the end of the alternation
        rw [if_neg (show ¬((sibs[c]! != none32) = true) by simp [hnxt])] at hscan
        dsimp only at hscan
        rw [hnxt, scanAltGo_none] at hscan
        simp only [Prod.mk.injEq] at hscan
        obtain ⟨-, ha, ho⟩ := hscan
        subst ha
        subst ho
        have f6 := polyAdd_snd hover
        have f5 := polyAdd_snd f6
        have f4 := polyAdd_snd f5
        have v4 := polyAdd_le f4 n
        have v5 := polyAdd_le f5 n
        have v6 := polyAdd_le f6 n
        have v7 := polyAdd_le hover n
        rw [hlo, hhi] at hkw hkr hkt
        refine ⟨polyAdd_snd f4, fun _ => ⟨?_, ?_, ?_⟩⟩
        · have m2 : (acc.flow.val n + (prices[c]!).outs.val n) * W hi ≤
              (polyAdd acc.flow (prices[c]!).outs
                (polyAdd acc.trail (prices[c]!).trail _).2).1.val n * W hi :=
            Nat.mul_le_mul_right _ v7
          rw [Nat.add_mul] at m2
          dsimp only
          omega
        · have m2 : (acc.flow.val n + (prices[c]!).outs.val n) * R hi ≤
              (polyAdd acc.flow (prices[c]!).outs
                (polyAdd acc.trail (prices[c]!).trail _).2).1.val n * R hi :=
            Nat.mul_le_mul_right _ v7
          rw [Nat.add_mul] at m2
          dsimp only
          omega
        · have m2 : (acc.flow.val n + (prices[c]!).outs.val n) * T hi ≤
              (polyAdd acc.flow (prices[c]!).outs
                (polyAdd acc.trail (prices[c]!).trail _).2).1.val n * T hi :=
            Nat.mul_le_mul_right _ v7
          rw [Nat.add_mul] at m2
          dsimp only
          omega

/-! ## What `cert_shape` says about the code

`costAt` reads a pricing off the code only if control moves forward, and the
bytecode does not carry that on its own. `cert_shape` does. A straight-line
region's walk refuses a split or a jump by name, so everything such a region
holds itself moves by one. An alternation's does not, and `shape_alt` is
what pins those: the split before a branch goes to the branch, its second
arm to the instruction after that branch's closing jump, and the jump to the
end of the alternation — all of them later than the instruction that named
them.

`CodeOk` is what the pricing needs at one instruction, and `region_code_ok`
walks the region tree downwards to establish it over every region's range.
The root's range is the whole program, so that is where the global fact
comes from.

One clause is not read off `cert_shape` and is kept as a hypothesis instead:
that an alternation's own end is inside the program. Every branch's closing
jump targets it and so does the last split's second arm, so an alternation
that ended the program would send the run off the end of the code. It is the
same hole the standing Accept hypothesis covers, and it is left explicit for
the same reason — the compiler emits an `Accept` after everything, and
whether the checker should be refusing programs that do not is a question
for BOUNDS.md.
-/

/-- BOUNDS.md section 4.3's shape: an optional item is one split at the head
of the region whose two arms are the body and the exit, in whichever order
the greediness asks for, with the body walked as an ordinary span. -/
theorem shapeRepeat_opt {code : Array Inst} {reps : Array RepInfo}
    {regions : Array Region} {sibs : Array Nat} {at_ first : Nat}
    (hhead : (code[(regions[at_]!).lo]!).op = .split)
    (h : shapeRepeat code reps regions sibs at_ first = .crOk) :
    (regions[at_]!).lo < (regions[at_]!).hi ∧
      (((code[(regions[at_]!).lo]!).arg = (regions[at_]!).lo + 1 ∧
          (code[(regions[at_]!).lo]!).alt = (regions[at_]!).hi) ∨
        ((code[(regions[at_]!).lo]!).arg = (regions[at_]!).hi ∧
          (code[(regions[at_]!).lo]!).alt = (regions[at_]!).lo + 1)) ∧
      shapeSpan code regions sibs ((regions[at_]!).lo + 1) (regions[at_]!).hi
        first = .crOk := by
  rw [shapeRepeat] at h
  dsimp only at h
  by_cases h1 : (regions[at_]!).hi ≤ (regions[at_]!).lo
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  rw [if_neg h1, if_pos hhead] at h
  by_cases h2 : ((code[(regions[at_]!).lo]!).arg = (regions[at_]!).lo + 1 ∧
      (code[(regions[at_]!).lo]!).alt = (regions[at_]!).hi) ∨
      ((code[(regions[at_]!).lo]!).arg = (regions[at_]!).hi ∧
        (code[(regions[at_]!).lo]!).alt = (regions[at_]!).lo + 1)
  · rw [if_neg (by rcases h2 with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b])] at h
    exact ⟨by omega, h2, h⟩
  · rw [if_pos (by
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]
      constructor
      · by_cases ha : (code[(regions[at_]!).lo]!).arg = (regions[at_]!).lo + 1
        · exact Or.inr (fun hb => h2 (Or.inl ⟨ha, hb⟩))
        · exact Or.inl ha
      · by_cases ha : (code[(regions[at_]!).lo]!).arg = (regions[at_]!).hi
        · exact Or.inr (fun hb => h2 (Or.inr ⟨ha, hb⟩))
        · exact Or.inl ha)] at h
    exact absurd h (by decide)

/-- And its price: the body's, with one visit, one backtrack entry and one
way out added — the way out being the arm that skips the body, which is a
way to leave the region like any other. -/
theorem scanRepeat_opt {code : Array Inst} {reps : Array RepInfo}
    {regions : Array Region} {prices : Array Price} {sibs : Array Nat}
    {at_ first n : Nat} {acc' : Acc} {over over' : Bool}
    (hhead : (code[(regions[at_]!).lo]!).op = .split)
    (h : scanRepeat code reps regions prices sibs at_ first over =
      (.crOk, acc', over')) (hover : over' = false) :
    ∃ acc : Acc,
      scanSpan code regions prices sibs ((regions[at_]!).lo + 1)
          (regions[at_]!).hi first (Acc.fresh (Poly.const 1)) over =
        (.crOk, acc, false) ∧
      acc.work.val n + 1 ≤ acc'.work.val n ∧
      acc.stack.val n + 1 ≤ acc'.stack.val n ∧
      acc'.trail = acc.trail ∧
      acc.flow.val n + 1 ≤ acc'.flow.val n := by
  rw [scanRepeat] at h
  dsimp only at h
  by_cases h1 : (regions[at_]!).hi ≤ (regions[at_]!).lo
  · rw [if_pos h1] at h
    simp only [Prod.mk.injEq] at h
    exact absurd h.1 (by decide)
  rw [if_neg h1, if_pos hhead] at h
  rcases hspan : scanSpan code regions prices sibs ((regions[at_]!).lo + 1)
      (regions[at_]!).hi first (Acc.fresh (Poly.const 1)) over with ⟨v, a, o⟩
  rw [hspan] at h
  dsimp only at h
  by_cases hv : v ≠ .crOk
  · rw [if_pos hv] at h
    simp only [Prod.mk.injEq] at h
    exact absurd h.1 hv
  rw [if_neg hv] at h
  simp only [ne_eq, Decidable.not_not] at hv
  subst hv
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, hacc, hov⟩ := h
  subst hover
  have f3 : (polyAdd a.stack (Poly.const 1)
      (polyAdd a.work (Poly.const 1) o).2).2 = false := polyAdd_snd hov
  have f2 : (polyAdd a.work (Poly.const 1) o).2 = false := polyAdd_snd f3
  have f1 : o = false := polyAdd_snd f2
  subst f1
  have vw := polyAdd_le f2 n
  have vs := polyAdd_le f3 n
  have vf := polyAdd_le hov n
  rw [Poly.val_const] at vw vs vf
  refine ⟨a, rfl, ?_, ?_, ?_, ?_⟩ <;> rw [← hacc] <;> dsimp only <;> omega

/-- What the pricing needs of one instruction: an opcode that is not a
repetition's, and, if it forks or jumps, targets that are ahead of it and
inside the program. Everything `costAt` asks of the code is here. -/
def CodeOk (re : Re) (q : Nat) : Prop :=
  ((re.code[q]!).op.loose = true ∨ (re.code[q]!).op = .split ∨
      (re.code[q]!).op = .jump) ∧
    ((re.code[q]!).op = .split →
      q < (re.code[q]!).arg ∧ (re.code[q]!).arg < re.code.size ∧
        q < (re.code[q]!).alt ∧ (re.code[q]!).alt < re.code.size) ∧
    ((re.code[q]!).op = .jump →
      q < (re.code[q]!).arg ∧ (re.code[q]!).arg < re.code.size)

/-- An instruction a region may hold loose satisfies it outright: `loose`
already excludes the split, the jump and the four repetition opcodes. -/
theorem CodeOk.ofLoose {re : Re} {q : Nat} (h : (re.code[q]!).op.loose = true) :
    CodeOk re q := by
  refine ⟨Or.inl h, ?_, ?_⟩ <;> intro hop <;> rw [hop] at h <;> exact absurd h (by decide)

/-- The section 4.1 walk read as coverage rather than as a price: whatever
holds of every loose opcode and of every child's range holds of the whole
range, because those two are all a straight-line region contains. The walk
refuses anything else by name. -/
theorem scanSpanGo_covers {code : Array Inst} {regions : Array Region}
    {prices : Array Price} {sibs : Array Nat} {hi : Nat} {Q : Nat → Prop}
    (hloose : ∀ q, (code[q]!).op.loose = true → Q q)
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      (regions[c]!).hi ≤ hi ∧
        ∀ q, (regions[c]!).lo ≤ q → q < (regions[c]!).hi → Q q) :
    ∀ (k pc cursor : Nat), P cursor → hi - pc ≤ k →
      ∀ (acc acc' : Acc) (over over' : Bool),
      scanSpanGo code regions prices sibs hi pc cursor acc over =
        (.crOk, acc', over') →
      ∀ q, pc ≤ q → q < hi → Q q := by
  intro k
  induction k with
  | zero =>
      intro pc cursor hP hk acc acc' over over' h q h1 h2
      omega
  | succ k ih =>
      intro pc cursor hP hk acc acc' over over' h q h1 h2
      by_cases hpc : pc < hi
      · rw [scanSpanGo, dif_pos hpc] at h
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
          split at h
          · exact absurd h (by simp)
          rename_i hkhi
          dsimp only at h
          obtain ⟨hchi, hcov⟩ := hkid cursor hP hcond.1
          by_cases hin : q < (regions[cursor]!).hi
          · exact hcov q (by rw [hcond.2]; omega) hin
          · exact ih (regions[cursor]!).hi (sibs[cursor]!) (hsib cursor hP hcond.1)
              (by omega) _ _ _ _ h q (by omega) h2
        · rename_i hcond
          dsimp only at h
          split at h
          all_goals rename_i hop
          all_goals
            first
              | (simp only [Prod.mk.injEq] at h
                 exact absurd h.1 (by decide))
              | (rcases Nat.eq_or_lt_of_le h1 with rfl | h3
                 · exact hloose _ (by rw [hop]; rfl)
                 · exact ih (pc + 1) _ hP (by omega) _ _ _ _ h q (by omega) h2)
      · omega



set_option maxHeartbeats 1000000 in
/-- The same for an alternation, off `shape_alt` rather than off the price
walk: its range is a split, a branch, a jump, and the rest of the chain, and
`shape_alt` has pinned each split and each jump to a later instruction. The
end of the alternation has to be inside the program, which is what the jumps
and the last split's second arm target. -/
theorem shapeAltGo_ok {re : Re} {sibs : Array Nat} {hi : Nat}
    (hhi : hi < re.code.size)
    (P : Nat → Prop) (hsib : ∀ c : Nat, P c → c ≠ none32 → P (sibs[c]!))
    (hle : ∀ c : Nat, P c → c ≠ none32 →
      (re.regions[c]!).lo ≤ (re.regions[c]!).hi)
    (hkid : ∀ c : Nat, P c → c ≠ none32 →
      ∀ q, (re.regions[c]!).lo ≤ q → q < (re.regions[c]!).hi → CodeOk re q) :
    ∀ (fuel p c k : Nat), P c →
      shapeAltGo re.code re.regions sibs hi fuel p c k = .crOk → c ≠ none32 →
      ∀ q, p ≤ q → q < hi → CodeOk re q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p c k hP h hne q h1 h2
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
          refine ⟨Or.inr (Or.inl hforkop), ?_, ?_⟩
          · intro _
            rw [harg, halt]
            omega
          · intro hj
            rw [hforkop] at hj
            exact absurd hj (by decide)
        by_cases hq2 : q < (re.regions[c]!).hi
        · exact hkid c hP hne q (by omega) hq2
        by_cases hq3 : q = (re.regions[c]!).hi
        · subst hq3
          refine ⟨Or.inr (Or.inr hleaveop), ?_, ?_⟩
          · intro hs
            rw [hleaveop] at hs
            exact absurd hs (by decide)
          · intro _
            rw [hleavearg]
            omega
        · exact ih ((re.regions[c]!).hi + 1) (sibs[c]!) (k + 1) (hsib c hP hne)
            hrec hnxt q (by omega) h2
      · exact hkid c hP hne q (by omega) (by omega)

/-- What `cert_shape`'s dispatch settled at one region: the walk its kind
asks for accepted. -/
def ShapeOk (re : Re) (kids sibs : Array Nat) (i : Nat) : Prop :=
  (match (re.regions[i]!).kind with
    | .root | .group | .branch =>
        shapeSpan re.code re.regions sibs (re.regions[i]!).lo
          (re.regions[i]!).hi kids[i]!
    | .alt => shapeAlt re.code re.regions sibs i kids[i]!
    | .«repeat» => shapeRepeat re.code re.reps re.regions sibs i kids[i]!) = .crOk

/-- One step of that dispatch, and then every region it reached. -/
theorem certShapeWalk_step {re : Re} {kids sibs : Array Nat} {i fuel : Nat}
    (h : certShapeWalk re kids sibs i (fuel + 1) = .crOk) :
    ShapeOk re kids sibs i ∧ certShapeWalk re kids sibs (i + 1) fuel = .crOk := by
  rw [certShapeWalk] at h
  unfold ShapeOk
  cases hk : (re.regions[i]!).kind
  all_goals rw [hk] at h
  all_goals dsimp only at h
  all_goals
    (split at h
     · rename_i hv
       exact absurd h hv
     rename_i hv
     simp only [ne_eq, Decidable.not_not] at hv
     exact ⟨hv, h⟩)

theorem certShapeWalk_all {re : Re} {kids sibs : Array Nat} :
    ∀ (fuel i : Nat), certShapeWalk re kids sibs i fuel = .crOk →
      ∀ j, i ≤ j → j < i + fuel → ShapeOk re kids sibs j := by
  intro fuel
  induction fuel with
  | zero =>
      intro i h j h1 h2
      omega
  | succ fuel ih =>
      intro i h j h1 h2
      obtain ⟨hstep, hnext⟩ := certShapeWalk_step h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hstep
      · exact ih (i + 1) hnext j (by omega) (by omega)

/-- A program `cert_shape` accepted ran the dispatch to the end. -/
theorem certShape_walk {re : Re} (h : certShape re = .crOk) :
    certShapeWalk re (regionKids re.regions).1 (regionKids re.regions).2 0
      re.regions.size = .crOk := by
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
  · exact h



/-- An alternation of no branches is refused, so an accepted one has a
first branch to walk. -/
theorem shapeAltGo_none {code : Array Inst} {regions : Array Region}
    {sibs : Array Nat} {hi fuel p : Nat}
    (h : shapeAltGo code regions sibs hi fuel p none32 0 = .crOk) : False := by
  cases fuel with
  | zero =>
      rw [shapeAltGo, if_neg (by simp), if_pos (by omega)] at h
      exact absurd h (by decide)
  | succ f =>
      rw [shapeAltGo, if_pos (by simp), if_pos (by omega)] at h
      exact absurd h (by decide)

theorem shapeAlt_first_ne {re : Re} {sibs : Array Nat} {i first : Nat}
    (h : shapeAlt re.code re.regions sibs i first = .crOk) : first ≠ none32 := by
  intro hf
  subst hf
  exact shapeAltGo_none h

/-- The tree induction that establishes it: a straight-line region's range
is covered by its own walk and by its children, an alternation's by
`shape_alt` and by its branches, and every child comes after its parent — so
walking the index downwards covers every region's range, and the root's
range is the program. -/
theorem region_code_ok {re : Re} {prices : Array Price}
    (hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i)
    (hnest : ∀ i, 1 ≤ i → i < re.regions.size →
      (re.regions[i]!).hi ≤ (re.regions[(re.regions[i]!).parent]!).hi)
    (hrange : ∀ i, i < re.regions.size →
      (re.regions[i]!).lo ≤ (re.regions[i]!).hi)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hshape : ∀ j, j < re.regions.size →
      ShapeOk re (regionKids re.regions).1 (regionKids re.regions).2 j)
    (hspan : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .root ∨ (re.regions[j]!).kind = .group ∨
        (re.regions[j]!).kind = .branch) →
      ∃ acc : Acc, scanSpan re.code re.regions prices (regionKids re.regions).2
        (re.regions[j]!).lo (re.regions[j]!).hi (regionKids re.regions).1[j]!
        (Acc.fresh (Poly.const 1)) false = (.crOk, acc, false))
    (hbody : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      ∃ acc : Acc, scanSpan re.code re.regions prices (regionKids re.regions).2
        ((re.regions[j]!).lo + 1) (re.regions[j]!).hi
        (regionKids re.regions).1[j]! (Acc.fresh (Poly.const 1)) false =
        (.crOk, acc, false)) :
    ∀ (k i : Nat), re.regions.size - i ≤ k → i < re.regions.size →
      ∀ q, (re.regions[i]!).lo ≤ q → q < (re.regions[i]!).hi → CodeOk re q := by
  intro k
  induction k with
  | zero =>
      intro i hk hi q h1 h2
      omega
  | succ k ih =>
      intro i hk hi q h1 h2
      have hpos : 0 < re.regions.size := by omega
      have hkid : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          (re.regions[c]!).hi ≤ (re.regions[i]!).hi ∧
            ∀ q', (re.regions[c]!).lo ≤ q' → q' < (re.regions[c]!).hi →
              CodeOk re q' := by
        intro c hP hne
        rcases hP with rfl | ⟨hic, hcs, hpar⟩
        · exact absurd rfl hne
        · refine ⟨?_, fun q' g1 g2 => ih c (by omega) hcs q' g1 g2⟩
          have hle := hnest c (by omega) hcs
          rw [hpar] at hle
          exact hle
      have hsh := hshape i hi
      unfold ShapeOk at hsh
      by_cases hkalt : (re.regions[i]!).kind = .alt
      · rw [hkalt] at hsh
        dsimp only at hsh
        have hfirst := shapeAlt_first_ne hsh
        rw [shapeAlt] at hsh
        exact shapeAltGo_ok (hends i hi (Or.inl hkalt)) (ChildOf re.regions i)
          (fun c hP hne => regionKids_next hpos hord i c hP hne)
          (fun c hP hne => by
            rcases hP with rfl | ⟨-, hcs, -⟩
            · exact absurd rfl hne
            · exact hrange c hcs)
          (fun c hP hne => (hkid c hP hne).2)
          re.regions.size (re.regions[i]!).lo ((regionKids re.regions).1[i]!) 0
          (regionKids_first hpos hord i hi) hsh hfirst q h1 h2
      by_cases hkrep : (re.regions[i]!).kind = .«repeat»
      · rw [hkrep] at hsh
        dsimp only at hsh
        obtain ⟨hlt, harg, -⟩ := shapeRepeat_opt (hopt i hi hkrep) hsh
        have hhi := hends i hi (Or.inr hkrep)
        by_cases hq : q = (re.regions[i]!).lo
        · subst hq
          refine ⟨Or.inr (Or.inl (hopt i hi hkrep)), ?_, ?_⟩
          · intro _
            rcases harg with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b] <;> omega
          · intro hj
            rw [hopt i hi hkrep] at hj
            exact absurd hj (by decide)
        · obtain ⟨acc, hscan⟩ := hbody i hi hkrep
          rw [scanSpan] at hscan
          exact scanSpanGo_covers (fun q hq => CodeOk.ofLoose hq)
            (ChildOf re.regions i)
            (fun c hP hne => regionKids_next hpos hord i c hP hne) hkid
            ((re.regions[i]!).hi - ((re.regions[i]!).lo + 1))
            ((re.regions[i]!).lo + 1)
            ((regionKids re.regions).1[i]!) (regionKids_first hpos hord i hi)
            (by omega) _ _ _ _ hscan q (by omega) h2
      · have hkind : (re.regions[i]!).kind = .root ∨
            (re.regions[i]!).kind = .group ∨ (re.regions[i]!).kind = .branch := by
          cases hk2 : (re.regions[i]!).kind
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd hk2 hkalt
          · exact absurd hk2 hkrep
        obtain ⟨acc, hscan⟩ := hspan i hi hkind
        rw [scanSpan] at hscan
        exact scanSpanGo_covers (fun q hq => CodeOk.ofLoose hq)
          (ChildOf re.regions i)
          (fun c hP hne => regionKids_next hpos hord i c hP hne) hkid
          ((re.regions[i]!).hi - (re.regions[i]!).lo) (re.regions[i]!).lo
          ((regionKids re.regions).1[i]!) (regionKids_first hpos hord i hi)
          (by omega) _ _ _ _ hscan q h1 h2

/-! ## The tree induction that prices a whole program

Everything above is one region deep. This is the induction that composes it.
The clause it carries at a region is the one both walks produce: the pricing
at the region's first instruction is covered by the region's claimed `work`
plus its claimed `outs` times the pricing where control leaves it, and the
same for the trail against `trail` and the stack against `stack`.

At the root that clause is the whole program. The root's range is the whole
of the code and the pricing past the end of the code is nothing, so what
comes out is the root's claim bounding the pricing at the entry point —
exactly the three numbers `attemptsWithin_of_flow` asks for.
-/

/-- A program point the code does not have reads as the default instruction,
which is a `Char`. Every clause below that asks about a split or a jump is
therefore about a point inside the program, and none of them has to say
so. -/
theorem code_out_op {code : Array Inst} {p : Nat} (h : code.size ≤ p) :
    (code[p]!).op = .chr := by
  rw [getElem!_neg code p (by omega)]
  rfl

/-- So a program whose last instruction is an `Accept` has one: an empty
array reads as the default everywhere, and the default is a `Char`. -/
theorem code_size_pos {re : Re}
    (h : (re.code[re.code.size - 1]!).op = .accept) : 0 < re.code.size := by
  rcases Nat.eq_zero_or_pos re.code.size with hz | hp
  · rw [code_out_op (by omega)] at h
    exact absurd h (by decide)
  · exact hp

/-- So an opcode that is not that default names a point inside. -/
theorem flowCost_inside {re : Re} {p : Nat} {o : Op} (hop : (re.code[p]!).op = o)
    (hne : o ≠ .chr) : p < re.code.size := by
  rcases Nat.lt_or_ge p re.code.size with h | h
  · exact h
  · rw [code_out_op h] at hop
    exact absurd hop.symm hne

/-- The three clauses `scanAltGo_priced` asks for at a split. -/
theorem flowCost_split_facts {re : Re}
    (hfwd : ∀ q, q < re.code.size → Inst.forward re.code q) (p : Nat)
    (hop : (re.code[p]!).op = .split) :
    flowCost re.code unitVisit p ≤ 1 + flowCost re.code unitVisit (re.code[p]!).arg
        + flowCost re.code unitVisit (re.code[p]!).alt ∧
      flowCost re.code unitRecord p ≤ flowCost re.code unitRecord (re.code[p]!).arg
        + flowCost re.code unitRecord (re.code[p]!).alt ∧
      flowCost re.code unitPush p ≤ 1 + flowCost re.code unitPush (re.code[p]!).arg
        + flowCost re.code unitPush (re.code[p]!).alt := by
  have hpc := flowCost_inside hop (by decide)
  have hnesave : (re.code[p]!).op ≠ .save := by rw [hop]; decide
  refine ⟨?_, ?_, ?_⟩
  · rw [flowCost_split hfwd hpc hop, unitVisit]
    omega
  · rw [flowCost_split hfwd hpc hop, unitRecord_ne hnesave]
    omega
  · rw [flowCost_split hfwd hpc hop, unitPush_split hop]
    omega

/-- And at a jump. -/
theorem flowCost_jump_facts {re : Re}
    (hfwd : ∀ q, q < re.code.size → Inst.forward re.code q) (p : Nat)
    (hop : (re.code[p]!).op = .jump) :
    flowCost re.code unitVisit p ≤ 1 + flowCost re.code unitVisit (re.code[p]!).arg ∧
      flowCost re.code unitRecord p ≤ flowCost re.code unitRecord (re.code[p]!).arg ∧
      flowCost re.code unitPush p ≤ flowCost re.code unitPush (re.code[p]!).arg := by
  have hpc := flowCost_inside hop (by decide)
  have hnesave : (re.code[p]!).op ≠ .save := by rw [hop]; decide
  have hnesplit : (re.code[p]!).op ≠ .split := by rw [hop]; decide
  refine ⟨?_, ?_, ?_⟩
  · rw [flowCost_jump hfwd hpc hop, unitVisit]
    omega
  · rw [flowCost_jump hfwd hpc hop, unitRecord_ne hnesave]
    omega
  · rw [flowCost_jump hfwd hpc hop, unitPush_ne hnesplit]
    omega

/-- And the ones `scanSpanGo_priced` asks for at everything else: one visit,
an undo entry only at a `Save`, no backtrack entry at all, and an `Accept`
that costs its own visit and nothing after it. -/
theorem flowCost_span_facts {re : Re}
    (hfwd : ∀ q, q < re.code.size → Inst.forward re.code q) (pc : Nat)
    (hpc : pc < re.code.size) (h2 : (re.code[pc]!).op ≠ .split)
    (h3 : (re.code[pc]!).op ≠ .jump) :
    (flowCost re.code unitVisit pc ≤ 1 + flowCost re.code unitVisit (pc + 1) ∧
        flowCost re.code unitRecord pc ≤ 1 + flowCost re.code unitRecord (pc + 1) ∧
        flowCost re.code unitPush pc ≤ flowCost re.code unitPush (pc + 1)) ∧
      ((re.code[pc]!).op ≠ .save →
        flowCost re.code unitRecord pc ≤ flowCost re.code unitRecord (pc + 1)) ∧
      ((re.code[pc]!).op = .accept →
        flowCost re.code unitVisit pc ≤ 1 ∧ flowCost re.code unitRecord pc = 0 ∧
          flowCost re.code unitPush pc = 0) := by
  by_cases hacc : (re.code[pc]!).op = .accept
  · have hnesave : (re.code[pc]!).op ≠ .save := by rw [hacc]; decide
    have hv := flowCost_accept (unit := unitVisit) hfwd hpc hacc
    have hr := flowCost_accept (unit := unitRecord) hfwd hpc hacc
    have ht := flowCost_accept (unit := unitPush) hfwd hpc hacc
    rw [unitRecord_ne hnesave] at hr
    rw [unitPush_ne h2] at ht
    rw [unitVisit] at hv
    exact ⟨⟨by omega, by omega, by omega⟩, fun _ => by omega,
      fun _ => ⟨by omega, hr, ht⟩⟩
  · have hv := flowCost_step (unit := unitVisit) hfwd hpc hacc h2 h3
    have hr := flowCost_step (unit := unitRecord) hfwd hpc hacc h2 h3
    have ht := flowCost_step (unit := unitPush) hfwd hpc hacc h2 h3
    rw [unitPush_ne h2] at ht
    rw [unitVisit] at hv
    refine ⟨⟨by omega, ?_, by omega⟩, ?_, fun hx => absurd hx hacc⟩
    · by_cases hs : (re.code[pc]!).op = .save
      · rw [unitRecord_save hs] at hr
        omega
      · rw [unitRecord_ne hs] at hr
        omega
    · intro hs
      rw [unitRecord_ne hs] at hr
      omega



/-- The tree induction, spending the measure `cert_shape` left behind. Every
region comes after its parent, so walking the index downwards prices a
region from prices that are already there, and the clause it establishes is
the same whatever the kind: the pricing at the region's first instruction is
covered by the region's claimed `work` plus its claimed `outs` times the
pricing where control leaves it.

A straight-line region gets that from `scanSpanGo_priced`, an alternation
from `scanAltGo_priced`, and an optional item from the two of them together
— its head is one forward split and its body is an ordinary span. `hopt` is
what keeps the counted repetition out: its pricing would have to name the
counter, and this one names only the program point. -/
theorem region_priced {re : Re} {prices : Array Price} {n : Nat}
    (hfwd : ∀ q, q < re.code.size → Inst.forward re.code q)
    (hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i)
    (hnest : ∀ i, 1 ≤ i → i < re.regions.size →
      (re.regions[i]!).hi ≤ (re.regions[(re.regions[i]!).parent]!).hi)
    (hin : ∀ i, i < re.regions.size → (re.regions[i]!).hi ≤ re.code.size)
    (hlo : ∀ i, i < re.regions.size → (re.regions[i]!).lo ≤ (re.regions[i]!).hi)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hsize : prices.size = re.regions.size)
    (hshape : ∀ j, j < re.regions.size →
      ShapeOk re (regionKids re.regions).1 (regionKids re.regions).2 j)
    (hprice : ∀ j, j < re.regions.size →
      RegionPriced re prices (regionKids re.regions).1 (regionKids re.regions).2 j) :
    ∀ (k i : Nat), re.regions.size - i ≤ k → i < re.regions.size →
      flowCost re.code unitVisit (re.regions[i]!).lo ≤ (prices[i]!).work.val n
          + (prices[i]!).outs.val n *
            flowCost re.code unitVisit (re.regions[i]!).hi ∧
        flowCost re.code unitRecord (re.regions[i]!).lo ≤ (prices[i]!).trail.val n
          + (prices[i]!).outs.val n *
            flowCost re.code unitRecord (re.regions[i]!).hi ∧
        flowCost re.code unitPush (re.regions[i]!).lo ≤ (prices[i]!).stack.val n
          + (prices[i]!).outs.val n *
            flowCost re.code unitPush (re.regions[i]!).hi := by
  intro k
  induction k with
  | zero =>
      intro i hk hi
      omega
  | succ k ih =>
      intro i hk hi
      have hpos : 0 < re.regions.size := by omega
      have hkid : ∀ c : Nat, ChildOf re.regions i c → c ≠ none32 →
          flowCost re.code unitVisit (re.regions[c]!).lo ≤ (prices[c]!).work.val n
              + (prices[c]!).outs.val n *
                flowCost re.code unitVisit (re.regions[c]!).hi ∧
            flowCost re.code unitRecord (re.regions[c]!).lo ≤
              (prices[c]!).trail.val n + (prices[c]!).outs.val n *
                flowCost re.code unitRecord (re.regions[c]!).hi ∧
            flowCost re.code unitPush (re.regions[c]!).lo ≤
              (prices[c]!).stack.val n + (prices[c]!).outs.val n *
                flowCost re.code unitPush (re.regions[c]!).hi := by
        intro c hP hne
        rcases hP with rfl | ⟨hic, hcs, hpar⟩
        · exact absurd rfl hne
        · exact ih c (by omega) hcs
      by_cases hkalt : (re.regions[i]!).kind = .alt
      · obtain ⟨acc, hscan, hdw, hdo, hds, hdt⟩ := (hprice i hi).alt hkalt
        have hsh := hshape i hi
        unfold ShapeOk at hsh
        rw [hkalt] at hsh
        dsimp only at hsh
        have hfirst := shapeAlt_first_ne hsh
        rw [shapeAlt] at hsh
        rw [scanAlt, hsize] at hscan
        obtain ⟨-, hrest⟩ :=
          scanAltGo_priced (n := n) (ChildOf re.regions i)
            (fun c hP hne => regionKids_next hpos hord i c hP hne)
            (flowCost_split_facts hfwd) (flowCost_jump_facts hfwd) hkid
            re.regions.size (re.regions[i]!).lo ((regionKids re.regions).1[i]!) 0
            _ _ _ _ (regionKids_first hpos hord i hi) hsh hscan rfl
        obtain ⟨hw, hr, ht⟩ := hrest hfirst
        simp only [Acc.fresh, Poly.val_zero, Nat.zero_mul, Nat.zero_add] at hw hr ht
        have mw := Nat.mul_le_mul_right (flowCost re.code unitVisit
          (re.regions[i]!).hi) (polyGe_sound hdo n)
        have mr := Nat.mul_le_mul_right (flowCost re.code unitRecord
          (re.regions[i]!).hi) (polyGe_sound hdo n)
        have mt := Nat.mul_le_mul_right (flowCost re.code unitPush
          (re.regions[i]!).hi) (polyGe_sound hdo n)
        have dw := polyGe_sound hdw n
        have ds := polyGe_sound hds n
        have dt := polyGe_sound hdt n
        exact ⟨by omega, by omega, by omega⟩
      by_cases hkrep : (re.regions[i]!).kind = .«repeat»
      · obtain ⟨acc, hscan, hdw, hdo, hds, hdt⟩ := (hprice i hi).rep hkrep
        have hsh := hshape i hi
        unfold ShapeOk at hsh
        rw [hkrep] at hsh
        dsimp only at hsh
        obtain ⟨hlt, harg, -⟩ := shapeRepeat_opt (hopt i hi hkrep) hsh
        obtain ⟨a, hspan, vw, vs, vt, vf⟩ :=
          scanRepeat_opt (n := n) (hopt i hi hkrep) hscan rfl
        rw [scanSpan] at hspan
        obtain ⟨-, hw, hr, ht⟩ :=
          scanSpanGo_priced (n := n)
            (fun pc hpc h2 h3 =>
              flowCost_span_facts hfwd pc (by have := hin i hi; omega) h2 h3)
            (ChildOf re.regions i)
            (fun c hP hne => regionKids_next hpos hord i c hP hne)
            (fun c hP hne _ => by
              refine ⟨(hkid c hP hne).1, (hkid c hP hne).2.1, (hkid c hP hne).2.2, ?_⟩
              rcases hP with rfl | ⟨hic, hcs, hpar⟩
              · exact absurd rfl hne
              · have hle := hnest c (by omega) hcs
                rw [hpar] at hle
                exact hle)
            ((re.regions[i]!).hi - ((re.regions[i]!).lo + 1))
            ((re.regions[i]!).lo + 1) ((regionKids re.regions).1[i]!)
            (regionKids_first hpos hord i hi) (by omega) (by omega)
            _ _ _ _ hspan rfl
        simp only [Acc.fresh, Poly.val_zero, Poly.val_const, Nat.one_mul,
          Nat.zero_add] at hw hr ht
        obtain ⟨sw, sr, st⟩ :=
          flowCost_split_facts hfwd (re.regions[i]!).lo (hopt i hi hkrep)
        have dw := polyGe_sound hdw n
        have dov := polyGe_sound hdo n
        have ds := polyGe_sound hds n
        have dt := polyGe_sound hdt n
        rw [vt] at dt
        have mw : (a.flow.val n + 1) *
            flowCost re.code unitVisit (re.regions[i]!).hi ≤
            (prices[i]!).outs.val n *
              flowCost re.code unitVisit (re.regions[i]!).hi :=
          Nat.mul_le_mul_right _ (by omega)
        have mr : (a.flow.val n + 1) *
            flowCost re.code unitRecord (re.regions[i]!).hi ≤
            (prices[i]!).outs.val n *
              flowCost re.code unitRecord (re.regions[i]!).hi :=
          Nat.mul_le_mul_right _ (by omega)
        have mt : (a.flow.val n + 1) *
            flowCost re.code unitPush (re.regions[i]!).hi ≤
            (prices[i]!).outs.val n *
              flowCost re.code unitPush (re.regions[i]!).hi :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at mw mr mt
        rcases harg with ⟨ha, hb⟩ | ⟨ha, hb⟩
        all_goals rw [ha, hb] at sw sr st
        all_goals exact ⟨by omega, by omega, by omega⟩
      · have hkind : (re.regions[i]!).kind = .root ∨
            (re.regions[i]!).kind = .group ∨ (re.regions[i]!).kind = .branch := by
          cases hk2 : (re.regions[i]!).kind
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd hk2 hkalt
          · exact absurd hk2 hkrep
        obtain ⟨acc, hscan, hdw, hdo, hds, hdt⟩ := (hprice i hi).span hkind
        rw [scanSpan] at hscan
        obtain ⟨-, hw, hr, ht⟩ :=
          scanSpanGo_priced (n := n)
            (fun pc hpc h2 h3 =>
              flowCost_span_facts hfwd pc (by have := hin i hi; omega) h2 h3)
            (ChildOf re.regions i)
            (fun c hP hne => regionKids_next hpos hord i c hP hne)
            (fun c hP hne _ => by
              refine ⟨(hkid c hP hne).1, (hkid c hP hne).2.1, (hkid c hP hne).2.2, ?_⟩
              rcases hP with rfl | ⟨hic, hcs, hpar⟩
              · exact absurd rfl hne
              · have hle := hnest c (by omega) hcs
                rw [hpar] at hle
                exact hle)
            ((re.regions[i]!).hi - (re.regions[i]!).lo) (re.regions[i]!).lo
            ((regionKids re.regions).1[i]!) (regionKids_first hpos hord i hi)
            (by omega) (hlo i hi)
            _ _ _ _ hscan rfl
        simp only [Acc.fresh, Poly.val_zero, Poly.val_const, Nat.one_mul,
          Nat.zero_add] at hw hr ht
        have mw := Nat.mul_le_mul_right (flowCost re.code unitVisit
          (re.regions[i]!).hi) (polyGe_sound hdo n)
        have mr := Nat.mul_le_mul_right (flowCost re.code unitRecord
          (re.regions[i]!).hi) (polyGe_sound hdo n)
        have mt := Nat.mul_le_mul_right (flowCost re.code unitPush
          (re.regions[i]!).hi) (polyGe_sound hdo n)
        have dw := polyGe_sound hdw n
        have ds := polyGe_sound hds n
        have dt := polyGe_sound hdt n
        exact ⟨by omega, by omega, by omega⟩

/-! ## R-6, R-7 and R-8 with alternation

The pieces above meet here. `cert_shape` gives the tree its shape and, with
it, the forwardness the code-level pricing needs; the checker's own
induction gives every region a claim that dominates what its walk produced;
the tree induction turns those into a pricing of the whole program dominated
by the root's claim; and the fork account turns that into what one entry
into the program spends.

What is left over is stated rather than hidden. Beyond an accepted
certificate the theorems below ask for three things the checker does not
test: that the tree holds no counted repetition, that the program ends in an
`Accept`, and that no alternation's own end is the end of the program. The
first is the honest boundary of this pricing; the other two are the same
hole, one level apart, and every program the compiler emits has neither.
-/

/-- Every region's range ends inside the program: the root's is the program
and every other region's is inside its parent's. -/
theorem region_hi_le {re : Re} (h : certShape re = .crOk) :
    ∀ (k i : Nat), i ≤ k → i < re.regions.size →
      (re.regions[i]!).hi ≤ re.code.size := by
  obtain ⟨-, -, -, hhi0⟩ := certShape_root h
  intro k
  induction k with
  | zero =>
      intro i hik hi
      have hz : i = 0 := by omega
      subst hz
      omega
  | succ k ih =>
      intro i hik hi
      rcases Nat.eq_zero_or_pos i with hz | hz
      · subst hz
        omega
      · obtain ⟨hpar, -, -, hn⟩ := certShape_facts h i hz hi
        have := ih (re.regions[i]!).parent (by omega) (by omega)
        omega

/-- And no region's range is backwards. -/
theorem region_lo_le {re : Re} (h : certShape re = .crOk) (i : Nat)
    (hi : i < re.regions.size) : (re.regions[i]!).lo ≤ (re.regions[i]!).hi := by
  obtain ⟨-, -, hlo0, hhi0⟩ := certShape_root h
  rcases Nat.eq_zero_or_pos i with hz | hz
  · subst hz
    omega
  · exact (certShape_facts h i hz hi).2.1

/-- The two claims a context sizes its arrays from are the root region's
exactly, which is what lets the pricing be weighed against the
certificate's own fields. -/
theorem certCheck_bt_claims {re : Re} {cert : Cert}
    (h : certCheck re .backtrack cert = .crOk) :
    cert.stack = (cert.prices[0]!).stack ∧ cert.trail = (cert.prices[0]!).trail := by
  obtain ⟨hs, ht, -, ⟨over, hcharge⟩, -, -, -⟩ := certCheck_bt_spec h
  obtain ⟨-, -, hst, htr⟩ := chargeCall_dom hs ht hcharge 0
  exact ⟨hst, htr⟩

/-- Forwardness for a whole accepted program: the tree induction run at the
root, whose range is the code. -/
theorem code_ok_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size) :
    ∀ q, q < re.code.size → CodeOk re q := by
  obtain ⟨-, -, -, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨hpos, -, hlo0, hhi0⟩ := certShape_root hshape
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape)
  have hpr := certCheckRegions_all re.regions.size 0 over hregions
  intro q hq
  exact region_code_ok (prices := cert.prices)
    (fun i h1 h2 => (certShape_facts hshape i h1 h2).1)
    (fun i h1 h2 => (certShape_facts hshape i h1 h2).2.2.2)
    (region_lo_le hshape) hopt hends
    (fun j hj => hsh j (Nat.zero_le _) (by omega))
    (fun j hj hk => ((hpr j (Nat.zero_le _) (by omega)).span hk).imp
      (fun _ hx => hx.1))
    (fun j hj hk => by
      obtain ⟨acc, hs, -, -, -, -⟩ := (hpr j (Nat.zero_le _) (by omega)).rep hk
      exact (scanRepeat_opt (n := 0) (hopt j hj hk) hs rfl).imp
        (fun _ hx => hx.1))
    re.regions.size 0 (by omega) hpos q (by omega) (by omega)

/-- And the pricing itself. Three hypotheses do the work `cert_shape` does
not do: that the program's last instruction is an `Accept`, so a
fall-through never leaves the code; that no alternation and no optional item
ends the program, so a closing jump and a skipped body never do either; and
that every repeat region in the tree is an optional item rather than a
counted repetition, which is where this pricing stops. -/
theorem flow_of_cert {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept) :
    Flow re (fun pc => pc < re.code.size) (flowCost re.code unitVisit)
      (flowCost re.code unitRecord) (flowCost re.code unitPush) := by
  have hsized : 0 < re.code.size := code_size_pos hlast
  have hok := code_ok_of_cert hcert hopt hends
  refine flow_of_forward (fun q hq => ⟨fun hs => ⟨((hok q hq).2.1 hs).1,
      ((hok q hq).2.1 hs).2.2.1⟩, fun hj => ((hok q hq).2.2 hj).1⟩)
    (fun pc h => h) (fun pc h => (hok pc h).1) ?_
  intro pc h
  refine ⟨fun hs => ⟨((hok pc h).2.1 hs).2.1, ((hok pc h).2.1 hs).2.2.2⟩,
    fun hj => ((hok pc h).2.2 hj).2, fun h2 h3 hacc => ?_⟩
  rcases Nat.lt_or_ge (pc + 1) re.code.size with hlt | hge
  · exact hlt
  · have hpe : pc = re.code.size - 1 := by omega
    exact absurd (hpe ▸ hlast) hacc

/-- Section 4 for a tree of groups, alternations and optional items: one
entry into the program visits at most the root region's claimed `work`,
records at most its `trail` and never pushes past its `stack`.

Four hypotheses beyond an accepted certificate, and every one of them is
something the checker does not ask about. Every repeat region is an optional
item, which is the boundary of this pricing — a counted repetition jumps
back to its own head, so what is still to come from that point depends on
the counter and not on the program point alone. The program ends in an
`Accept`, which is the standing hypothesis of this file. No alternation and
no optional item ends the program, which is the same hypothesis one level
down: a branch's closing jump and a skipped body both target the end of
their region, so a region that ended the program would send the run off the
end of the code. And the caller's memory limit sits inside the allocation
ceiling, which is what makes the growth schedule double. -/
theorem attemptsWithin_forward {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size) := by
  have hsized : 0 < re.code.size := code_size_pos hlast
  obtain ⟨-, -, hsize, -, hshape, over, hregions⟩ := certCheck_bt_spec hcert
  obtain ⟨hpos, -, hlo0, hhi0⟩ := certShape_root hshape
  obtain ⟨hstc, htrc⟩ := certCheck_bt_claims hcert
  have hok := code_ok_of_cert hcert hopt hends
  have hfwd : ∀ q, q < re.code.size → Inst.forward re.code q :=
    fun q hq => ⟨fun hs => ⟨((hok q hq).2.1 hs).1, ((hok q hq).2.1 hs).2.2.1⟩,
      fun hj => ((hok q hq).2.2 hj).1⟩
  have hpr := certCheckRegions_all re.regions.size 0 over hregions
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape)
  obtain ⟨hw, hr, ht⟩ := region_priced (n := s.size) hfwd
    (fun i h1 h2 => (certShape_facts hshape i h1 h2).1)
    (fun i h1 h2 => (certShape_facts hshape i h1 h2).2.2.2)
    (fun i hi => region_hi_le hshape i i (Nat.le_refl _) hi)
    (region_lo_le hshape) hopt hsize
    (fun j hj => hsh j (Nat.zero_le _) (by omega))
    (fun j hj => hpr j (Nat.zero_le _) (by omega))
    re.regions.size 0 (by omega) hpos
  have h0v : flowCost re.code unitVisit re.code.size = 0 :=
    flowCost_out (Nat.le_refl _)
  have h0r : flowCost re.code unitRecord re.code.size = 0 :=
    flowCost_out (Nat.le_refl _)
  have h0t : flowCost re.code unitPush re.code.size = 0 :=
    flowCost_out (Nat.le_refl _)
  rw [hlo0, hhi0, h0v, Nat.mul_zero, Nat.add_zero] at hw
  rw [hlo0, hhi0, h0r, Nat.mul_zero, Nat.add_zero] at hr
  rw [hlo0, hhi0, h0t, Nat.mul_zero, Nat.add_zero] at ht
  refine attemptsWithin_of_flow (flow_of_cert hcert hopt hends hlast) hlim
    hsized hw ?_ ?_
  · rw [htrc]
    exact hr
  · rw [hstc]
    exact ht

/-- R-6 for a pattern with groups, alternation and optional items, nested as
deep as it likes. -/
theorem btRun_cost_le_forward {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size :=
  btRun_cost_le hcert
    (attemptsWithin_forward hcert hopt hends hlast hlim)

/-- R-7 on the same programs. Unlike the group nest, the backtrack stack
really is used here, and `outs` is what pays for it. -/
theorem btRun_stack_le_forward {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  btRun_stack_le (attemptsWithin_forward hcert hopt hends hlast hlim)

/-- And R-8. The trail is used here too, so the memory line is no longer the
setup alone. -/
theorem btRun_mem_le_forward {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hopt : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .«repeat» →
      (re.code[(re.regions[j]!).lo]!).op = .split)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size :=
  btRun_mem_le hcert (attemptsWithin_forward hcert hopt hends hlast hlim)

/-! ### The alternation-only class, with the repeat clause discharged -/

/-- Section 4 for a tree that adds alternation to the group nest and nothing
else: the repeat clause above has nothing to say, because there is no repeat
region for it to say it about. -/
theorem attemptsWithin_alt {re : Re} {s : ByteArray} {mo : MOpts}
    {lim : Limits} {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hnorep : ∀ j, j < re.regions.size → (re.regions[j]!).kind ≠ .«repeat»)
    (hends : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .alt →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    AttemptsWithin re s mo lim start (btSetup re) (cert.stack.val s.size)
      (cert.trail.val s.size) ((cert.prices[0]!).work.val s.size) :=
  attemptsWithin_forward hcert (fun j hj hk => absurd hk (hnorep j hj))
    (fun j hj hk => hends j hj (hk.resolve_right (hnorep j hj))) hlast hlim

/-- R-6 on that class. -/
theorem btRun_cost_le_alt {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hnorep : ∀ j, j < re.regions.size → (re.regions[j]!).kind ≠ .«repeat»)
    (hends : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .alt →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.cost ≤ cert.cost.val s.size :=
  btRun_cost_le hcert (attemptsWithin_alt hcert hnorep hends hlast hlim)

/-- R-7. -/
theorem btRun_stack_le_alt {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hnorep : ∀ j, j < re.regions.size → (re.regions[j]!).kind ≠ .«repeat»)
    (hends : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .alt →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.stack ≤ cert.stack.val s.size :=
  btRun_stack_le (attemptsWithin_alt hcert hnorep hends hlast hlim)

/-- And R-8. -/
theorem btRun_mem_le_alt {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hnorep : ∀ j, j < re.regions.size → (re.regions[j]!).kind ≠ .«repeat»)
    (hends : ∀ j, j < re.regions.size → (re.regions[j]!).kind = .alt →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hlim : lim.mem ≤ ceiling) :
    (btRun re s start mo lim 0 0).usage.mem ≤ cert.mem.val s.size :=
  btRun_mem_le hcert (attemptsWithin_alt hcert hnorep hends hlast hlim)

end Pcrevera.Ref
