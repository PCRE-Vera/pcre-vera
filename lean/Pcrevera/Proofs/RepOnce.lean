import Pcrevera.Proofs.RepPriced

/-!
# One region per counted repetition (BOUNDS.md section 4.4)

The pricing of section 4.4 carries two numbers per repetition — how ambiguous
its body is, and what one pass through it charges — while the checker reads
them off a region. The two agree only if a repetition index names one region
and no more, and both directions of that agreement are needed, so a bound on
the number of regions naming one repetition is of no use: it has to be one.

`counted_regions_agree` already says that two counted repeat regions naming
one repetition cover the same range, because a counted region *is* its
record's range. What is left is that one range belongs to one region, and
that is a fact about the tree rather than about the code.

The argument runs on three things `cert_shape` settles and nothing has read
back yet. Its nesting pass forbids two children of one region from
overlapping, which together with the parent order makes containment ancestry:
of two regions sharing a position, the earlier one is an ancestor of the
later. Its dispatch pass walks a counted region's body between the `RepEnter`
and the `RepNext`, so every child of such a region begins at least three
instructions past its own start. And `region_kids` files every region under
its parent, so a child the body walk never meets is a child that is not
there.

That last one is where the sentinel shows. The engine indexes regions with a
`u32` and spells NONE as `0xFFFFFFFF`, so a real region and the sentinel are
distinguishable by construction; the Lean reference indexes with `Nat` and
gets no such promise, and a program with `0xFFFFFFFF + 1` regions would have
one whose index reads as NONE and which therefore hangs off no parent's child
list at all. That region is invisible to every walk in the checker, both the
shape one and the price one, so it can be a second counted region over one
range. The theorems below carry `re.regions.size ≤ none32` for it, the same
way the resource bounds carry the existence of an `Accept`.
-/

namespace Pcrevera.Ref

open Pcrevera

/-! ## Siblings do not overlap -/

/-- Writing a slot that is not the sentinel leaves every slot non-sentinel
that already was, whether or not the write lands. -/
theorem set!_ne_none32 {a : Array Nat} {q v p : Nat} (hv : v ≠ none32)
    (hp : a[p]! ≠ none32) : (a.set! q v)[p]! ≠ none32 := by
  by_cases hpq : p = q
  · subst hpq
    by_cases hb : p < a.size
    · rw [getElem!_set!_self _ _ _ hb]
      exact hv
    · rw [getElem!_neg (a.set! p v) p (by simpa using hb), getElem!_neg a p hb] at *
      exact hp
  · rw [getElem!_set!_ne _ _ _ _ hpq]
    exact hp

/-- The overlap rule of the nesting pass, read as a fact about the tree.
`ends` remembers where the last child of each region stopped, and a child
starting before that is refused; since a region's range is not backwards,
what `ends` holds only ever grows, so the rule reaches back over every
earlier child rather than over the previous one alone. -/
theorem certShapeNest_sibs {regions : Array Region} :
    ∀ (fuel i : Nat) (ends : Array Nat), ends.size = regions.size →
      i + fuel ≤ regions.size →
      (∀ j, 1 ≤ j → j < i → (regions[j]!).hi ≤ ends[(regions[j]!).parent]!) →
      certShapeNest regions i fuel ends = none →
      ∀ j j', 1 ≤ j → j < j' → i ≤ j' → j' < i + fuel →
        (regions[j]!).parent = (regions[j']!).parent →
        (regions[j]!).hi ≤ (regions[j']!).lo := by
  intro fuel
  induction fuel with
  | zero =>
      intro i ends _ _ _ _ j j' _ _ _ h4 _
      omega
  | succ fuel ih =>
      intro i ends hsize hbnd hinv h j j' h1 h2 h3 h4 hpar
      rw [certShapeNest] at h
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      rename_i hord
      split at h
      · exact absurd h (by simp)
      rename_i hrange
      split at h
      · exact absurd h (by simp)
      split at h
      · exact absurd h (by simp)
      rename_i hover
      split at h
      · exact absurd h (by simp)
      simp only [Nat.not_le, Nat.not_lt] at hord hrange hover
      have hself : (regions[i]!).parent < ends.size := by omega
      rcases Nat.eq_or_lt_of_le h3 with rfl | h5
      · have := hinv j h1 (by omega)
        rw [hpar] at this
        omega
      · refine ih (i + 1) _ (by simp [hsize]) (by omega) (fun p g1 g2 => ?_) h j j'
          h1 h2 (by omega) (by omega) hpar
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ g2) with rfl | g3
        · rw [getElem!_set!_self _ _ _ hself]
          exact Nat.le_refl _
        · by_cases hq : (regions[p]!).parent = (regions[i]!).parent
          · rw [hq, getElem!_set!_self _ _ _ hself]
            have := hinv p g1 g3
            rw [hq] at this
            omega
          · rw [getElem!_set!_ne _ _ _ _ hq]
            exact hinv p g1 g3

/-- And so two regions with one parent cover disjoint ranges, in index
order. -/
theorem certShape_sibs {re : Re} (h : certShape re = .crOk) {j j' : Nat}
    (h1 : 1 ≤ j) (h2 : j < j') (h3 : j' < re.regions.size)
    (hpar : (re.regions[j]!).parent = (re.regions[j']!).parent) :
    (re.regions[j]!).hi ≤ (re.regions[j']!).lo :=
  certShapeNest_sibs (re.regions.size - 1) 1 _ (by simp) (by omega)
    (fun _ g1 g2 => by omega) (certShape_nest h) j j' h1 h2 (by omega) (by omega)
    hpar

/-! ## Containment is ancestry -/

/-- Two regions sharing a position are nested, and the earlier one is the
outer: it has a child whose range still covers the later one whole.

The parent order is what makes this an induction. A region's parent covers it
and comes before it, so the two regions and the later one's parent stand in
one of three ways, and two of them are the same problem over a smaller index.
The third has both regions hanging off one parent by different children,
which the sibling rule refuses because the position they share would have to
sit in two disjoint ranges. -/
theorem region_ancestor {re : Re} (h : certShape re = .crOk) :
    ∀ (k b a q : Nat), b ≤ k → a < b → b < re.regions.size →
      (re.regions[a]!).lo ≤ q → q < (re.regions[a]!).hi →
      (re.regions[b]!).lo ≤ q → q < (re.regions[b]!).hi →
      ∃ c, 1 ≤ c ∧ c < re.regions.size ∧ (re.regions[c]!).parent = a ∧
        a < c ∧ c ≤ b ∧ (re.regions[c]!).lo ≤ (re.regions[b]!).lo ∧
        (re.regions[b]!).hi ≤ (re.regions[c]!).hi := by
  intro k
  induction k with
  | zero =>
      intro b a q hbk hab _ _ _ _ _
      omega
  | succ k ih =>
      intro b a q hbk hab hb h1 h2 h3 h4
      obtain ⟨hpord, -, hplo, hphi⟩ := certShape_facts h b (by omega) hb
      rcases Nat.lt_trichotomy (re.regions[b]!).parent a with hlt | heq | hgt
      · obtain ⟨e, he1, hes, hepar, hpe, hea, helo, hehi⟩ :=
          ih a (re.regions[b]!).parent q (by omega) hlt (by omega) (by omega)
            (by omega) h1 h2
        exact absurd (certShape_sibs h he1 (by omega) hb hepar) (by omega)
      · exact ⟨b, by omega, hb, heq, hab, Nat.le_refl _, Nat.le_refl _,
          Nat.le_refl _⟩
      · obtain ⟨c, hc1, hcs, hcpar, hac, hcp, hclo, hchi⟩ :=
          ih (re.regions[b]!).parent a q (by omega) hgt (by omega) h1 h2
            (by omega) (by omega)
        exact ⟨c, hc1, hcs, hcpar, hac, by omega, by omega, by omega⟩

/-! ## Every child is on a child list -/

/-- `region_kids` never clears a child list it has filled: the pass writes
region indices, and a region index is not the sentinel. -/
theorem regionKidsGo_keeps {regions : Array Region} :
    ∀ (i : Nat) (kids sibs : Array Nat), i < none32 → ∀ p : Nat,
      kids[p]! ≠ none32 → (regionKidsGo regions i kids sibs).1[p]! ≠ none32 := by
  intro i
  induction i with
  | zero =>
      intro kids sibs _ p hp
      rw [regionKidsGo]
      exact hp
  | succ i ih =>
      intro kids sibs hi p hp
      rw [regionKidsGo]
      exact ih _ _ (by omega) p (set!_ne_none32 (by omega) hp)

/-- And it does fill one for every region it walks, since it files each of
them under the parent it names. -/
theorem regionKidsGo_files {regions : Array Region} :
    ∀ (i : Nat) (kids sibs : Array Nat), kids.size = regions.size →
      i < none32 → ∀ c, 1 ≤ c → c ≤ i → (regions[c]!).parent < regions.size →
        (regionKidsGo regions i kids sibs).1[(regions[c]!).parent]! ≠ none32 := by
  intro i
  induction i with
  | zero =>
      intro kids sibs _ _ c h1 h2 _
      omega
  | succ i ih =>
      intro kids sibs hk hi c h1 h2 hp
      rw [regionKidsGo]
      rcases Nat.eq_or_lt_of_le h2 with rfl | h3
      · refine regionKidsGo_keeps i _ _ (by omega) _ ?_
        rw [getElem!_set!_self _ _ _ (by omega)]
        omega
      · exact ih _ _ (by simp [hk]) (by omega) c h1 (by omega) hp

/-- So a region the sentinel cannot be mistaken for is filed under its own
parent, whose child list is therefore not the empty one. -/
theorem regionKids_files {regions : Array Region} (hsz : regions.size ≤ none32)
    (c : Nat) (h1 : 1 ≤ c) (h2 : c < regions.size)
    (hp : (regions[c]!).parent < regions.size) :
    (regionKids regions).1[(regions[c]!).parent]! ≠ none32 := by
  rw [regionKids]
  exact regionKidsGo_files (regions.size - 1) _ _ (by simp) (by omega) c h1
    (by omega) hp

/-! ## Where a span walk's first child sits -/

/-- The child a span walk is holding when it starts lies inside the range it
is walking, and covers something. The walk meets its children in code order,
so one behind the cursor is refused outright; one it never reaches is left
over at the end, which is refused too; and one it does reach is entered, which
is where the emptiness and the far end get tested. -/
theorem shapeSpanGo_cursor {code : Array Inst} {regions : Array Region}
    {sibs : Array Nat} {hi : Nat} :
    ∀ (k pc cursor : Nat), hi - pc ≤ k → cursor ≠ none32 →
      shapeSpanGo code regions sibs hi pc cursor = .crOk →
      pc ≤ (regions[cursor]!).lo ∧
        (regions[cursor]!).lo < (regions[cursor]!).hi ∧
        (regions[cursor]!).hi ≤ hi := by
  intro k
  induction k with
  | zero =>
      intro pc cursor hk hne h
      rw [shapeSpanGo, dif_neg (by omega), if_pos (by simpa using hne)] at h
      exact absurd h (by decide)
  | succ k ih =>
      intro pc cursor hk hne h
      by_cases hlt : pc < hi
      · rw [shapeSpanGo, dif_pos hlt] at h
        by_cases hback : (cursor != none32 && (regions[cursor]!).lo < pc) = true
        · rw [if_pos hback] at h
          exact absurd h (by decide)
        rw [if_neg hback] at h
        have hge : pc ≤ (regions[cursor]!).lo := by
          rcases Nat.lt_or_ge (regions[cursor]!).lo pc with hcon | hcon
          · exact absurd (by simp [hne, hcon] :
              (cursor != none32 && (regions[cursor]!).lo < pc) = true) hback
          · exact hcon
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
          exact ⟨hge, by omega, by omega⟩
        rw [if_neg hhit] at h
        split at h
        all_goals
          first
            | exact absurd h (by decide)
            | (obtain ⟨-, g2, g3⟩ := ih (pc + 1) cursor (by omega) hne h
               exact ⟨hge, g2, g3⟩)
      · rw [shapeSpanGo, dif_neg hlt, if_pos (by simpa using hne)] at h
        exact absurd h (by decide)

/-! ## One region per repetition -/

/-- A counted repeat region has no other region over its range.

Take the two to be distinct and the earlier one counted. Containment is
ancestry, so the earlier one has a child that still covers the later one, and
that child covers the whole range: it starts where the counted region starts.
But the counted region's own walk begins three instructions in, past the
`RepZero`, the `RepLoop` and the `RepEnter`, so the child it holds starts
there or later and covers something. Those two are children of one region and
so cover disjoint ranges, whichever way round they are, which they do not. -/
theorem counted_regions_absurd {re : Re} (hshape : certShape re = .crOk)
    (hsz : re.regions.size ≤ none32) {a b : Nat} (hab : a < b)
    (hb : b < re.regions.size) (hkind : (re.regions[a]!).kind = .«repeat»)
    (hz : (re.code[(re.regions[a]!).lo]!).op = .repZero)
    (hlo : (re.regions[a]!).lo = (re.regions[b]!).lo)
    (hhi : (re.regions[a]!).hi = (re.regions[b]!).hi) : False := by
  have hpos : 0 < re.regions.size := by omega
  have ha : a < re.regions.size := by omega
  have hord : ∀ i, 1 ≤ i → i < re.regions.size → (re.regions[i]!).parent < i :=
    fun i g1 g2 => (certShape_facts hshape i g1 g2).1
  have hsh := certShapeWalk_all re.regions.size 0 (certShape_walk hshape) a
    (Nat.zero_le _) (by omega)
  unfold ShapeOk at hsh
  rw [hkind] at hsh
  dsimp only at hsh
  obtain ⟨h4, -, -, -, -, -, -, -, -, -, -, hspan⟩ := shapeRepeat_counted hz hsh
  obtain ⟨c, hc1, hcs, hcpar, hac, -, hclo, hchi⟩ :=
    region_ancestor hshape b b a (re.regions[a]!).lo (Nat.le_refl _) hab hb
      (Nat.le_refl _) (by omega) (by omega) (by omega)
  obtain ⟨-, -, hcnlo, hcnhi⟩ := certShape_facts hshape c hc1 hcs
  rw [hcpar] at hcnlo hcnhi
  have hdne : (regionKids re.regions).1[a]! ≠ none32 := by
    have hf := regionKids_files hsz c hc1 hcs (by rw [hcpar]; omega)
    rw [hcpar] at hf
    exact hf
  rcases regionKids_first hpos hord a ha with hn | ⟨had, hds, hdpar⟩
  · exact hdne hn
  rw [shapeSpan] at hspan
  obtain ⟨g1, g2, g3⟩ := shapeSpanGo_cursor (hi := (re.regions[a]!).hi - 1)
    ((re.regions[a]!).hi - 1 - ((re.regions[a]!).lo + 3))
    ((re.regions[a]!).lo + 3) ((regionKids re.regions).1[a]!) (Nat.le_refl _)
    hdne hspan
  rcases Nat.lt_trichotomy c (regionKids re.regions).1[a]! with hlt | heq | hgt
  · exact absurd (certShape_sibs hshape hc1 hlt hds (by rw [hcpar, hdpar]))
      (by omega)
  · rw [heq] at hclo
    omega
  · exact absurd (certShape_sibs hshape (by omega) hgt hcs (by rw [hdpar, hcpar]))
      (by omega)

/-- And so a repetition index names one counted repeat region and no more,
which is what the pricing of section 4.4 reads its two numbers through. -/
theorem counted_regions_once {re : Re} (hshape : certShape re = .crOk)
    (hsz : re.regions.size ≤ none32) {i i' : Nat}
    (hi : i < re.regions.size) (hi' : i' < re.regions.size)
    (hkind : (re.regions[i]!).kind = .«repeat»)
    (hkind' : (re.regions[i']!).kind = .«repeat»)
    (hz : (re.code[(re.regions[i]!).lo]!).op = .repZero)
    (hz' : (re.code[(re.regions[i']!).lo]!).op = .repZero)
    (harg : (re.code[(re.regions[i']!).lo]!).arg =
      (re.code[(re.regions[i]!).lo]!).arg) : i = i' := by
  obtain ⟨hlo, hhi⟩ :=
    counted_regions_agree hshape hi hi' hkind hkind' hz hz' harg
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact (counted_regions_absurd hshape hsz hlt hi' hkind hz hlo hhi).elim
  · exact heq
  · exact
      (counted_regions_absurd hshape hsz hgt hi hkind' hz' hlo.symm hhi.symm).elim

/-! ## Section 4.4's two halves, with the tree read back -/

/-- `rep_cert_priced_choose` with its uniqueness hypothesis discharged: every
head of the program is priced, and one entry into it is inside the root
region's claim, off an accepted certificate and the two standing hypotheses
the forward pricing already carries.

What is left beside them is that a region index and the NONE sentinel are
different numbers, which the engine has by construction and the reference,
indexing with `Nat`, does not. -/
theorem rep_cert_priced_once {re : Re} {cert : Cert}
    (hcert : certCheck re .backtrack cert = .crOk)
    (hends : ∀ j, j < re.regions.size →
      ((re.regions[j]!).kind = .alt ∨ (re.regions[j]!).kind = .«repeat») →
      (re.regions[j]!).hi < re.code.size)
    (hlast : (re.code[re.code.size - 1]!).op = .accept)
    (hsz : re.regions.size ≤ none32) (n : Nat) :
    (∀ (regs : Array UInt32) (pos : Nat),
        repCost re unitVisitR n (repWays re cert.prices n)
            (repChargeW re cert.prices n) 0 regs pos ≤
            (cert.prices[0]!).work.val n ∧
          repCost re unitRecordR n (repWays re cert.prices n)
            (repChargeR re cert.prices n) 0 regs pos ≤ cert.trail.val n ∧
          repCost re unitPushR n (repWays re cert.prices n)
            (repChargeT re cert.prices n) 0 regs pos ≤ cert.stack.val n) ∧
      ∀ q : Nat, (re.code[q]!).op = .repLoop →
        RepPassPriced re n (repWays re cert.prices n)
          (repChargeW re cert.prices n) (repChargeR re cert.prices n)
          (repChargeT re cert.prices n) q :=
  rep_cert_priced_choose hcert hends hlast
    (fun _ _ g1 g2 g3 g4 g5 g6 g7 =>
      counted_regions_once (certCheck_bt_spec hcert).2.2.2.2.1 hsz g1 g2 g3 g4 g5
        g6 g7) n

end Pcrevera.Ref
