import Pcrevera.Proofs.PikeBounds

namespace Pcrevera.Ref

open Pcrevera

/-! ### What the list step spends -/

private theorem foldl_size' {α : Type _} (f : Array α → Nat → Array α)
    (hf : ∀ a k, (f a k).size = a.size) : ∀ (l : List Nat) (p : Array α),
    (l.foldl f p).size = p.size := by
  intro l
  induction l with
  | nil => intro p; rfl
  | cons a l ih =>
      intro p
      rw [List.foldl_cons, ih, hf]

private theorem perm_last' (A : List Nat) (x : Nat) : (A ++ [x]).Perm (x :: A) := by
  have h := List.perm_middle (l₁ := A) (a := x) (l₂ := [])
  rwa [List.append_nil] at h

theorem listInRange_of_empty {re : Re} {a : Array Th} (h : a.size = 0) :
    listInRange re a := by
  have hnil : a.toList = [] :=
    List.eq_nil_of_length_eq_zero (by rwa [Array.length_toList])
  intro y hy
  rw [hnil] at hy
  simp at hy

theorem seen_ok_step {x : POut StepOut} {a : StepOut} {st : PikeSt}
    (he : x = .ok a) (h : (outSt StepOut.st x).seen = st.seen) :
    a.st.seen = st.seen := by
  rw [he] at h
  exact h

theorem dropRest_seen {lim : Limits} : ∀ (rest : List Th) (st : PikeSt),
    (outSt id (dropRest lim rest st)).seen = st.seen := by
  intro rest
  induction rest with
  | nil =>
      intro st
      rw [dropRest]
      rfl
  | cons th rest ih =>
      intro st
      rw [dropRest]
      split
      · rename_i he
        exact seen_of_error he pikeDrop_seen
      · rename_i he
        rw [ih]
        exact seen_ok_id he pikeDrop_seen

/-- Dropping the threads a recorded match outranks charges only growth, and
each block it frees has room on the free list because someone was holding
it. -/
theorem dropRest_charged {re : Re} {setup : Nat} {lim : Limits} (hwf : ReWf re) :
    ∀ (rest : List Th) (st : PikeSt) (L : List Nat), Rooms re st →
      st.m.mem = setup + st.reserved →
      Owned re.novec st.rc st.free st.pool (rest.map Th.h ++ L) →
      st.rc.size ≤ re.code.size * 4 + 2 →
      Charged re setup 0 st (outSt id (dropRest lim rest st)) := by
  intro rest
  induction rest with
  | nil =>
      intro st L hrooms hmem _ _
      rw [dropRest]
      exact Charged.idle hrooms rfl rfl hmem
  | cons th rest ih =>
      intro st L hrooms hmem hown htab
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: (rest.map Th.h ++ L)) := by simpa using hown
      have hch := pikeDrop_charged (setup := setup) (h := th.h) (lim := lim) hwf
        hrooms hmem (fun _ => free_room hmid htab)
      rw [dropRest]
      split
      · rename_i he
        exact charged_of_error he hch
      · rename_i stB hb
        have hchB : Charged re setup 0 st stB := charged_ok_id hb hch
        obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hb
        exact Charged.mono (hchB.trans (ih stB L hchB.rooms hchB.held
          (pikeDrop_owned hb hmid) (by rw [hrcB]; exact htab))) (by omega)

/-- At the last position the step opens no closure at all: a consuming
thread there fails the `pos < n` test and lets its handle go instead of
closing over. So the visited set the position cleared is charged and never
drawn on, which is what keeps a whole scan inside `n + 1` positions' worth
of marks rather than one set more. -/
theorem stepThreads_seen (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (start pos : Nat) (hpos : s.size ≤ pos) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      (outSt StepOut.st (stepThreads re s mo lim start pos threads st mh
        seeding matched)).seen = st.seen := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched
      rw [stepThreads]
      rfl
  | cons th rest ih =>
      intro st mh seeding matched
      have hstep : ∀ stB : PikeSt, stB.seen = st.seen →
          (outSt StepOut.st (stepThreads re s mo lim start pos rest stB mh
            seeding matched)).seen = st.seen := by
        intro stB hb
        rw [ih stB mh seeding matched]
        exact hb
      simp only [stepThreads]
      split
      · rfl
      · cases hop : (re.code[th.pc]!).op <;> dsimp only
        case chr | chrCI | cls | any | anyNoNL =>
          split
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            omega
          · split
            · rename_i he
              exact seen_of_error he pikeDrop_seen
            · rename_i he
              exact hstep _ (seen_ok_id he pikeDrop_seen)
        case accept =>
          split
          · split
            · rename_i he
              exact seen_of_error he pikeDrop_seen
            · rename_i he
              exact hstep _ (seen_ok_id he pikeDrop_seen)
          · split
            · rename_i he
              exact seen_of_error he pikeWrite_seen
            · rename_i stW hv he
              have h1 : stW.seen = st.seen := seen_ok_fst he pikeWrite_seen
              split
              · rename_i hd
                exact (seen_of_error hd pikeDrop_seen).trans h1
              · rename_i stD hd
                have h2 : stD.seen = st.seen :=
                  (seen_ok_id hd pikeDrop_seen).trans h1
                split
                · rename_i hr
                  exact (seen_of_error hr (dropRest_seen rest stD)).trans h2
                · rename_i hr
                  exact (seen_ok_id hr (dropRest_seen rest stD)).trans h2
        case bsr | split | jump | save | circ | circM | doll | dollE | dollM
            | sod | eod | eodn | wordB | notWordB | repZero | repLoop
            | repEnter | repNext =>
          all_goals
            split
            · rename_i he
              exact seen_of_error he pikeDrop_seen
            · rename_i he
              exact hstep _ (seen_ok_id he pikeDrop_seen)

set_option maxHeartbeats 4000000 in
/-- Stepping the built list, weighed. Each thread costs the one unit the loop
tests for before it charges it, and the closure it opens spends only what its
own marks release; the accept's copy-on-write is the one block a step pays
besides. So a step is inside a unit per thread and one block, whatever the
list does, and a refusal is inside it too. -/
theorem stepThreads_spent (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos setup : Nat) :
    ∀ (threads : List Th) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      BuildOk re st → st.stk.size = 0 →
      (∀ th ∈ threads, th.pc < re.code.size) →
      Rooms re st → st.m.mem = setup + st.reserved →
      Owned re.novec st.rc st.free st.pool
        (buildLive true st (threads.map Th.h ++ mhList mh)) →
      st.nlist.size + unmarked st.seen ≤ re.code.size →
      addMeasure true st + threads.length + 1 ≤ re.code.size * 3 + 1 →
      st.rc.size ≤ re.code.size * 4 + 2 →
      Spent re setup (threads.length + pikeBlock re) st
        (outSt StepOut.st (stepThreads re s mo lim start pos threads st mh
          seeding matched)) := by
  intro threads
  induction threads with
  | nil =>
      intro st mh seeding matched _ _ _ hrooms hmem _ _ _ _
      rw [stepThreads]
      exact Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _)
  | cons th rest ih =>
      intro st mh seeding matched hb hstk0 hpcs hrooms hmem hown hparked hreach
        htab
      have hC := hwf.sized
      have hthpc : th.pc < re.code.size := hpcs th List.mem_cons_self
      have hrest : ∀ t ∈ rest, t.pc < re.code.size :=
        fun t htm => hpcs t (List.mem_cons_of_mem _ htm)
      have hml : (mhList mh).length ≤ 1 := mhList_length mh
      -- The thread's own handle, taken into flight off the snapshot.
      have hmid : Owned re.novec st.rc st.free st.pool
          (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)) := by
        refine hown.perm ?_
        have he : (th :: rest).map Th.h ++ mhList mh =
            th.h :: (rest.map Th.h ++ mhList mh) := by simp
        rw [he, buildLive, buildLive]
        exact List.perm_middle.symm
      have hlenA := buildLive_length true st (rest.map Th.h ++ mhList mh)
      have hlen : (th.h :: buildLive true st (rest.map Th.h ++ mhList mh)).length
          ≤ re.code.size * 4 + 1 := by
        simp only [List.length_cons, List.length_append, List.length_map] at *
        omega
      have hmark : Charged re setup 1 st
          { st with m := { st.m with cost := st.m.cost + 1 } } :=
        Charged.pay 1 hrooms hmem
      have hstep : ∀ (stB : PikeSt) (c : Nat),
          BuildOk re stB → stB.stk.size = 0 →
          Rooms re stB → stB.m.mem = setup + stB.reserved →
          Owned re.novec stB.rc stB.free stB.pool
            (buildLive true stB (rest.map Th.h ++ mhList mh)) →
          stB.nlist.size + unmarked stB.seen ≤ re.code.size →
          addMeasure true stB + rest.length + 1 ≤ re.code.size * 3 + 1 →
          stB.rc.size ≤ re.code.size * 4 + 2 →
          Spent re setup c st stB → c ≤ 1 →
          Spent re setup ((th :: rest).length + pikeBlock re) st
            (outSt StepOut.st (stepThreads re s mo lim start pos rest stB mh
              seeding matched)) := by
        intro stB c h1 h2 h3 h4 h5 h6 h7 h8 hsp hc
        refine Spent.mono (hsp.trans (ih stB mh seeding matched h1 h2 hrest h3 h4
          h5 h6 h7 h8)) ?_
        simp only [List.length_cons]
        omega
      -- The three shapes an arm can take, read off the charged state.
      have harmAdd : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          th.pc + 1 < re.code.size →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h stA
              = .error stE →
            Spent re setup ((th :: rest).length + pikeBlock re) st stE) ∧
          (∀ stB, pikeAdd re s mo lim true (pos + 1) (th.pc + 1) th.h stA
              = .ok stB →
            Spent re setup ((th :: rest).length + pikeBlock re) st
              (outSt StepOut.st (stepThreads re s mo lim start pos rest stB mh
                seeding matched))) := by
        intro stA hchA hnext hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hbA : BuildOk re stA :=
          ⟨by rw [hseenA]; exact hb.seenSize, by rw [hstkA]; exact hb.stk,
            by rw [hclA]; exact hb.clist, by rw [hnlA]; exact hb.nlist⟩
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hmA : addMeasure true stA = addMeasure true st := by
          simp only [addMeasure, hstkA, hseenA, hpkA]
        have hadd := pikeAdd_spent re s mo lim hwf true (pos + 1) (th.pc + 1)
          th.h setup (rest.map Th.h ++ mhList mh) hbA.seenSize hbA.stk
          hchA.rooms hchA.held hownA (by rw [hstkA]; exact hstk0)
          (by rw [hpkA, hseenA]; exact hparked)
          (by
            simp only [List.length_append, List.length_map]
            simp only [List.length_cons] at hreach
            omega)
          (by rw [hrcA]; exact htab) hnext
        refine ⟨?_, ?_⟩
        · intro stE he
          refine Spent.mono
            ((Spent.ofCharged hchA hseenA).trans (spent_of_error he hadd)) ?_
          simp only [List.length_cons]
          omega
        · intro stB hok
          obtain ⟨b1, b2, b3, -⟩ := pikeAdd_build re s mo lim hwf true (pos + 1)
            (th.pc + 1) th.h hok hnext hbA
          obtain ⟨o1, o2, o3, o4, o5⟩ := pikeAdd_owned re s mo lim true (pos + 1)
            (th.pc + 1) th.h (rest.map Th.h ++ mhList mh) hok hbA.seenSize hownA
          have hspB : Spent re setup (1 + 0) st stB :=
            (Spent.ofCharged hchA hseenA).trans (spent_ok_id hok hadd)
          have hclB : stB.clist = stA.clist := b3 rfl
          have hnlB : stB.nlist.size + unmarked stB.seen ≤ re.code.size := by
            simp only [buildMeasure] at b2
            have hc := congrArg Array.size hclB
            have hn := congrArg Array.size hnlA
            rw [hseenA] at b2
            omega
          refine hstep stB (1 + 0) b1 o4 hspB.rooms hspB.held o1 hnlB ?_ ?_ hspB
            (by omega)
          · simp only [List.length_cons] at hreach
            omega
          · simp only [List.length_append, List.length_map] at o5
            simp only [List.length_cons] at hreach
            have hr := congrArg Array.size hrcA
            omega
      have harmDrop : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeDrop stA th.h lim = .error stE →
            Spent re setup ((th :: rest).length + pikeBlock re) st stE) ∧
          (∀ stB, pikeDrop stA th.h lim = .ok stB →
            Spent re setup ((th :: rest).length + pikeBlock re) st
              (outSt StepOut.st (stepThreads re s mo lim start pos rest stB mh
                seeding matched))) := by
        intro stA hchA hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hbA : BuildOk re stA :=
          ⟨by rw [hseenA]; exact hb.seenSize, by rw [hstkA]; exact hb.stk,
            by rw [hclA]; exact hb.clist, by rw [hnlA]; exact hb.nlist⟩
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hch := pikeDrop_charged (setup := setup) (h := th.h) (lim := lim)
          hwf hchA.rooms hchA.held
          (fun _ => free_room hownA (by rw [hrcA]; exact htab))
        have hsn := pikeDrop_seen (st := stA) (h := th.h) (lim := lim)
        refine ⟨?_, ?_⟩
        · intro stE he
          refine Spent.mono
            ((Spent.ofCharged hchA hseenA).trans
              (Spent.ofCharged (charged_of_error he hch)
                (seen_of_error he hsn))) ?_
          simp only [List.length_cons]
          omega
        · intro stB hok
          have hchB : Charged re setup 0 stA stB := charged_ok_id hok hch
          have hsnB : stB.seen = st.seen := (seen_ok_id hok hsn).trans hseenA
          obtain ⟨hstkB, hseB⟩ := pikeDrop_ok hok
          obtain ⟨hclB, hnlB⟩ := pikeDrop_lists hok
          obtain ⟨hrcB, -⟩ := pikeDrop_rcSize hok
          have hpkB : parkList true stB = parkList true st :=
            (parkList_eq hclB hnlB).trans hpkA
          have hspB : Spent re setup (1 + 0) st stB :=
            (Spent.ofCharged hchA hseenA).trans
              (Spent.ofCharged hchB ((seen_ok_id hok hsn)))
          refine hstep stB (1 + 0)
            ⟨by rw [hsnB]; exact hb.seenSize,
              by rw [hstkB, hstkA]; exact hb.stk,
              by rw [hclB, hclA]; exact hb.clist,
              by rw [hnlB, hnlA]; exact hb.nlist⟩
            (by rw [hstkB, hstkA]; exact hstk0) hspB.rooms hspB.held ?_ ?_ ?_ ?_
            hspB (by omega)
          · exact drop_owned hok hownA
          · have hnB : (parkList true stB).size = stB.nlist.size := rfl
            have hnS : (parkList true st).size = st.nlist.size := rfl
            have hsame := congrArg Array.size hpkB
            rw [hnB, hnS] at hsame
            rw [hsnB, hsame]
            exact hparked
          · simp only [addMeasure, hstkB, hstkA, hsnB, hpkB]
            simp only [addMeasure, List.length_cons] at hreach
            omega
          · rw [hrcB, hrcA]
            exact htab
      have harmAccept : ∀ (stA : PikeSt), Charged re setup 1 st stA →
          stA.seen = st.seen → stA.stk = st.stk → stA.clist = st.clist →
          stA.nlist = st.nlist → stA.rc = st.rc → stA.free = st.free →
          stA.pool = st.pool →
          (∀ stE, pikeWrite stA re.novec th.h 1 pos.toUInt32 lim = .error stE →
            Spent re setup ((th :: rest).length + pikeBlock re) st stE) ∧
          (∀ stW hv, pikeWrite stA re.novec th.h 1 pos.toUInt32 lim
              = .ok (stW, hv) →
            (∀ stE, pikeDrop stW mh lim = .error stE →
              Spent re setup ((th :: rest).length + pikeBlock re) st stE) ∧
            (∀ stD, pikeDrop stW mh lim = .ok stD →
              (∀ stE, dropRest lim rest stD = .error stE →
                Spent re setup ((th :: rest).length + pikeBlock re) st stE) ∧
              (∀ stF, dropRest lim rest stD = .ok stF →
                Spent re setup ((th :: rest).length + pikeBlock re) st stF))) := by
        intro stA hchA hseenA hstkA hclA hnlA hrcA hfreeA hpoolA
        have hpkA : parkList true stA = parkList true st := parkList_eq hclA hnlA
        have hblA : buildLive true stA (rest.map Th.h ++ mhList mh) =
            buildLive true st (rest.map Th.h ++ mhList mh) := by
          simp only [buildLive, hstkA, hpkA]
        have hownA : Owned re.novec stA.rc stA.free stA.pool
            (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)) := by
          rw [hrcA, hfreeA, hpoolA, hblA]
          exact hmid
        have hlenA' : (th.h :: buildLive true stA (rest.map Th.h ++ mhList mh)).length
            ≤ re.code.size * 4 + 1 := by
          rw [hblA]; exact hlen
        have hchW := pikeWrite_charged (setup := setup) (novec := re.novec)
          (h := th.h) (slot := 1) (value := pos.toUInt32) (lim := lim) hwf
          hchA.rooms hchA.held
          (fun hz => by have h2 := (take_room hownA hlenA' hz).1; omega)
          (fun hz => by
            have h2 := (take_room hownA hlenA' hz).2
            have hbb : re.code.size * 4 + 1 + 1 = re.code.size * 4 + 2 := by omega
            rwa [hbb] at h2)
        have hsnW := pikeWrite_seen (st := stA) (novec := re.novec) (h := th.h)
          (slot := 1) (value := pos.toUInt32) (lim := lim)
        have hbk : pikeBlock re = re.novec * regSize := rfl
        refine ⟨?_, ?_⟩
        · intro stE he
          refine Spent.mono
            ((Spent.ofCharged hchA hseenA).trans
              (Spent.ofCharged (charged_of_error he hchW)
                (seen_of_error he hsnW))) ?_
          simp only [List.length_cons, hbk]
          omega
        · intro stW hv hok
          have hspW : Spent re setup (1 + re.novec * regSize) st stW :=
            (Spent.ofCharged hchA hseenA).trans
              (Spent.ofCharged (charged_ok_fst hok hchW) (seen_ok_fst hok hsnW))
          obtain ⟨hownW, hszW⟩ := pikeWrite_owned hok hownA
          obtain ⟨hstkW, hseW⟩ := pikeWrite_ok hok
          obtain ⟨hclW, hnlW⟩ := pikeWrite_lists hok
          have hpkW : parkList true stW = parkList true stA :=
            parkList_eq hclW hnlW
          have htabW : stW.rc.size ≤ re.code.size * 4 + 2 := by
            have hr := congrArg Array.size hrcA
            simp only [List.length_cons] at hreach
            simp only [List.length_append, List.length_map] at hlenA
            have hbl := congrArg List.length hblA
            omega
          have hchD := pikeDrop_charged (setup := setup) (h := mh) (lim := lim)
            hwf hspW.rooms hspW.held (fun _ => free_room hownW htabW)
          have hsnD := pikeDrop_seen (st := stW) (h := mh) (lim := lim)
          refine ⟨?_, ?_⟩
          · intro stE he
            refine Spent.mono
              (hspW.trans (Spent.ofCharged (charged_of_error he hchD)
                (seen_of_error he hsnD))) ?_
            simp only [List.length_cons, hbk]
            omega
          · intro stD hd
            have hspD : Spent re setup (1 + re.novec * regSize + 0) st stD :=
              hspW.trans (Spent.ofCharged (charged_ok_id hd hchD)
                (seen_ok_id hd hsnD))
            obtain ⟨hrcD, -⟩ := pikeDrop_rcSize hd
            -- The old match let go of: a no-op while it is still the sentinel.
            have hdrop : Owned re.novec stD.rc stD.free stD.pool
                (hv :: buildLive true stW (rest.map Th.h)) := by
              by_cases hmh : mh = none32
              · subst hmh
                have hnil : mhList none32 = [] := by rw [mhList, if_pos rfl]
                have hres := pikeDrop_none_owned hd hownW
                rw [hblA] at hres
                rw [hnil, List.append_nil] at hres
                rw [buildLive, hstkW, hpkW, hstkA, hpkA, ← buildLive]
                exact hres
              · have hmhl : mhList mh = [mh] := by rw [mhList, if_neg hmh]
                refine pikeDrop_owned hd (how := ?_)
                refine hownW.perm ?_
                rw [hblA, hmhl]
                simp only [buildLive]
                have he : handles st.stk ++ handles (parkList true st) ++
                    (rest.map Th.h ++ [mh]) =
                    (handles st.stk ++ handles (parkList true st) ++
                      rest.map Th.h) ++ [mh] := by simp
                rw [he, hstkW, hpkW, hstkA, hpkA]
                exact (((perm_last' _ mh).cons hv).trans
                  (List.Perm.swap mh hv _)).symm
            have hrestL : Owned re.novec stD.rc stD.free stD.pool
                (rest.map Th.h ++
                  (hv :: (handles stW.stk ++ handles (parkList true stW)))) := by
              refine hdrop.perm ?_
              rw [buildLive]
              exact List.perm_middle.trans ((List.perm_append_comm).cons hv)
            have hchR := dropRest_charged (setup := setup) (lim := lim) hwf rest
              stD _ hspD.rooms hspD.held hrestL (by rw [hrcD]; exact htabW)
            have hsnR := dropRest_seen (lim := lim) rest stD
            refine ⟨?_, ?_⟩
            · intro stE he
              refine Spent.mono
                (hspD.trans (Spent.ofCharged (charged_of_error he hchR)
                  (seen_of_error he hsnR))) ?_
              simp only [List.length_cons, hbk]
              omega
            · intro stF hr
              refine Spent.mono
                (hspD.trans (Spent.ofCharged (charged_ok_id hr hchR)
                  (seen_ok_id hr hsnR))) ?_
              simp only [List.length_cons, hbk]
              omega
      simp only [stepThreads]
      split
      · exact Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _)
      cases hop : (re.code[th.pc]!).op <;>
        first
          | dsimp only
          | simp only [hop]
          | skip
      case chr | chrCI | cls | any | anyNoNL =>
        have hnext : th.pc + 1 < re.code.size :=
          hwf.targets _ hthpc _ (by simp [pikeTargets, hop])
        split
        · split
          · rename_i he
            exact (harmAdd _ hmark hnext rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmAdd _ hmark hnext rfl rfl rfl rfl rfl rfl rfl).2 _ he
        · split
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ he
      case accept =>
        split
        · split
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ he
        · split
          · rename_i he
            exact (harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            split
            · rename_i hd
              exact ((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                he).1 _ hd
            · rename_i hd
              split
              · rename_i hr
                exact (((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                  he).2 _ hd).1 _ hr
              · rename_i hr
                exact (((harmAccept _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ _
                  he).2 _ hd).2 _ hr
      case bsr | split | jump | save | circ | circM | doll | dollE | dollM
          | sod | eod | eodn | wordB | notWordB | repZero | repLoop
          | repEnter | repNext =>
        all_goals
          split
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).1 _ he
          · rename_i he
            exact (harmDrop _ hmark rfl rfl rfl rfl rfl rfl rfl).2 _ he

/-! ### What a position's seed spends -/

/-- Seeding a position: the block it takes is growth the reservation pays
for, the fill it charges is the one block BOUNDS.md section 9 names, and the
closure it opens spends only what its own marks release. -/
theorem pikeSeed_spent (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start pos setup : Nat) (ext : List Nat) {st : PikeSt}
    (hsz : st.seen.size = re.code.size) (hrange : listInRange re st.stk)
    (hstk0 : st.stk.size = 0) (hrooms : Rooms re st)
    (hmem : st.m.mem = setup + st.reserved)
    (hown : Owned re.novec st.rc st.free st.pool (buildLive false st ext))
    (hparked : (parkList false st).size + unmarked st.seen ≤ re.code.size)
    (hreach : addMeasure false st + ext.length + 1 ≤ re.code.size * 4)
    (htable : st.rc.size ≤ re.code.size * 4 + 2) :
    Spent re setup (pikeBlock re) st
      (outSt id (pikeSeed re s mo lim start pos st)) := by
  have hC := hwf.sized
  have hbk : pikeBlock re = re.novec * regSize := rfl
  have hlenB := buildLive_length false st ext
  have hlen : (buildLive false st ext).length ≤ re.code.size * 4 + 1 := by omega
  have hch := pikeTake_charged (setup := setup) (novec := re.novec) (lim := lim)
    hwf hrooms hmem
    (fun hz => by have h2 := (take_room hown hlen hz).1; omega)
    (fun hz => by
      have h2 := (take_room hown hlen hz).2
      have hbb : re.code.size * 4 + 1 + 1 = re.code.size * 4 + 2 := by omega
      rwa [hbb] at h2)
  have hsn := pikeTake_seen (st := st) (novec := re.novec) (lim := lim)
  simp only [pikeSeed]
  split
  · exact Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _)
  · split
    · rename_i he
      exact Spent.mono (Spent.ofCharged (charged_of_error he hch)
        (seen_of_error he hsn)) (Nat.zero_le _)
    · rename_i stT sh ht
      have hspT : Spent re setup 0 st stT :=
        Spent.ofCharged (charged_ok_fst ht hch) (seen_ok_fst ht hsn)
      obtain ⟨htake, hsize⟩ := pikeTake_owned ht hown
      obtain ⟨hstkT, hseenT⟩ := pikeTake_ok ht
      obtain ⟨hclT, hnlT⟩ := pikeTake_lists ht
      have hpkT : parkList false stT = parkList false st := parkList_eq hclT hnlT
      have hblT : buildLive false stT ext = buildLive false st ext := by
        simp only [buildLive, hstkT, hpkT]
      split
      · exact Spent.mono hspT (Nat.zero_le _)
      · have hpay : Charged re setup (re.novec * regSize) stT
            { stT with
              m := { stT.m with cost := stT.m.cost + re.novec * regSize } } :=
          Charged.pay _ hspT.rooms hspT.held
        have hfill : Charged re setup (re.novec * regSize) stT
            { stT with
              m := { stT.m with cost := stT.m.cost + re.novec * regSize }
              pool := ((List.range re.novec).foldl
                (fun (pool : Array UInt32) k =>
                  pool.set! (sh * re.novec + k) unset32) stT.pool).set!
                (sh * re.novec) pos.toUInt32 } := by
          refine Charged.mono (hpay.trans (Charged.idle ?_ ?_ rfl hpay.held))
            (by omega)
          · exact ⟨hpay.rooms.clist, hpay.rooms.nlist, hpay.rooms.stk,
              hpay.rooms.rc, hpay.rooms.free, hpay.rooms.pool⟩
          · rfl
        have hpsize : (((List.range re.novec).foldl
              (fun (pool : Array UInt32) k =>
                pool.set! (sh * re.novec + k) unset32) stT.pool).set!
              (sh * re.novec) pos.toUInt32).size = stT.pool.size := by
          rw [Array.size_set!]
          exact foldl_size' _ (fun a k => Array.size_set! _ _ _) _ _
        have hgo : ∀ stP : PikeSt, stP.clist = stT.clist →
            stP.nlist = stT.nlist → stP.stk = stT.stk → stP.seen = stT.seen →
            stP.rc = stT.rc → stP.free = stT.free →
            stP.pool.size = stT.pool.size →
            Charged re setup (re.novec * regSize) stT stP →
            Spent re setup (pikeBlock re) st
              (outSt id (pikeAdd re s mo lim false pos 0 sh stP)) := by
          intro stP hcl hnl hstk hseen hrc hfree hpl hch
          have hpkP : parkList false stP = parkList false stT :=
            parkList_eq hcl hnl
          have hblP : buildLive false stP ext = buildLive false st ext := by
            simp only [buildLive, hstk, hstkT, hpkP, hpkT]
          refine Spent.mono
            ((hspT.trans (Spent.ofCharged hch hseen)).trans
              (pikeAdd_spent re s mo lim hwf false pos 0 sh setup ext
                (by rw [hseen, hseenT]; exact hsz)
                (by rw [hstk, hstkT]; exact hrange) hch.rooms hch.held ?_
                (by rw [hstk, hstkT]; exact hstk0)
                (by rw [hpkP, hpkT, hseen, hseenT]; exact hparked) ?_ ?_
                hwf.sized)) (by omega)
          · rw [hrc, hfree, hblP]
            exact Owned.ofPool htake hpl
          · simp only [addMeasure]
            rw [hstk, hstkT, hseen, hseenT, hpkP, hpkT]
            simp only [addMeasure] at hreach
            omega
          · rw [hrc]
            have hml : (buildLive false st ext).length ≤ re.code.size * 4 := by
              omega
            omega
        exact hgo _ rfl rfl rfl rfl rfl rfl hpsize hfill

/-! ### What a position costs, and a whole scan -/

theorem closureLeftFull_le_position (re : Re) :
    closureLeftFull re + pikeBlock re ≤ pikePosition re := by
  have h := position_split re
  omega

set_option maxHeartbeats 4000000 in
/-- The position loop, weighed. Each iteration seeds, clears the visited set,
and steps the list it built, and those three together are exactly BOUNDS.md
section 9's `2*C + (S + 2)*B + W`: the clear hands the step and the next
position's seed one set's worth of marks between them, the seed pays a block,
the step a unit per thread and a block for the accept.

The account carries a full set on the left because that is what the run has
to show for the clear it made last: at the last position the step opens no
closure, so the set cleared there is charged and never drawn on, and it is
that leftover which pays for the seed at the very first position — where the
set came from `pike_run` rather than from a clear. -/
theorem pikeLoop_spent (re : Re) (s : ByteArray) (mo : MOpts) (lim : Limits)
    (hwf : ReWf re) (start : Nat) (anchored : Bool) (setup : Nat) :
    ∀ (steps pos : Nat) (st : PikeSt) (mh : Nat) (seeding matched : Bool),
      pos ≤ s.size → PosOk re st mh → Rooms re st →
      st.m.mem = setup + st.reserved →
      ∃ spent, Charged re setup spent st
          (pikeLoop re s mo lim start anchored (pikeWords re) steps pos st mh
            seeding matched).1 ∧
        spent + closureLeftFull re ≤
          closureLeft re st.seen + (s.size + 1 - pos) * pikePosition re := by
  intro steps
  induction steps with
  | zero =>
      intro pos st mh seeding matched hple hok hrooms hmem
      rw [pikeLoop]
      refine ⟨0, Charged.idle hrooms rfl rfl hmem, ?_⟩
      have hF := closureLeftFull_le_position re
      have h2 : pikePosition re ≤ (s.size + 1 - pos) * pikePosition re :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  | succ k ih =>
      intro pos st mh seeding matched hple hok hrooms hmem
      have hC := hwf.sized
      have hFp := closureLeftFull_le_position re
      have hone : pikePosition re ≤ (s.size + 1 - pos) * pikePosition re :=
        Nat.le_mul_of_pos_left _ (by omega)
      have htwo : pos < s.size →
          pikePosition re + pikePosition re ≤
            (s.size + 1 - pos) * pikePosition re := by
        intro hlt
        have h2 : 2 * pikePosition re ≤ (s.size + 1 - pos) * pikePosition re :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hml := mhList_length mh
      have hmeas := LoopOk.addMeasure_le hok.loop hok.stk
      -- The seed, and what it leaves.
      have hseed : Spent re setup (pikeBlock re) st
          (outSt id (if seeding && (!anchored || pos == start) then
            pikeSeed re s mo lim start pos st
            else (Except.ok st : POut PikeSt))) := by
        split
        · refine pikeSeed_spent re s mo lim hwf start pos setup (mhList mh)
            hok.loop.build.seenSize hok.loop.build.stk hok.stk hrooms hmem
            hok.owned ?_ ?_ hok.pool
          · have hb := hok.loop.bounded
            have hpk : (parkList false st).size = st.clist.size := rfl
            omega
          · omega
        · exact Spent.mono (Spent.refl hrooms hmem) (Nat.zero_le _)
      have hseeded : ∀ stS : PikeSt,
          (if seeding && (!anchored || pos == start) then
            pikeSeed re s mo lim start pos st
            else (Except.ok st : POut PikeSt)) = .ok stS →
          BuildOk re stS ∧
            stS.clist.size + stS.nlist.size + unmarked stS.seen ≤ re.code.size ∧
            stS.nlist.size = 0 ∧ stS.stk.size = 0 ∧
            Owned re.novec stS.rc stS.free stS.pool
              (buildLive false stS (mhList mh)) ∧
            stS.rc.size ≤ re.code.size * 4 + 2 := by
        intro stS hs
        have hbd := hok.loop.bounded
        have hem := hok.loop.empty
        have hp := hok.pool
        split at hs
        · obtain ⟨h1, h2, h3⟩ :=
            pikeSeed_build re s mo lim hwf start pos hs hok.loop.build
          obtain ⟨p1, p2, p3, p4, p5⟩ :=
            pikeSeed_owned re s mo lim start pos (mhList mh) hs
              hok.loop.build.seenSize hok.stk hok.owned
          simp only [buildMeasure] at h2
          have h3' := congrArg Array.size h3
          exact ⟨h1, by omega, by omega, p4, p1, by omega⟩
        · injection hs with hs
          subst hs
          exact ⟨hok.loop.build, by omega, hem, hok.stk, hok.owned, hok.pool⟩
      -- Cashing an exit out: the leftover of the last clear is what the
      -- account is missing, and a position that is not the last has a whole
      -- price still unspent.
      have hexit : ∀ stX : PikeSt, Spent re setup (pikePosition re) st stX →
          (s.size ≤ pos → closureLeft re stX.seen = closureLeftFull re) →
          ∃ spent, Charged re setup spent st stX ∧
            spent + closureLeftFull re ≤
              closureLeft re st.seen + (s.size + 1 - pos) * pikePosition re := by
        intro stX hsp hlast
        obtain ⟨sp, hc, hle⟩ := hsp
        refine ⟨sp, hc, ?_⟩
        rcases Nat.lt_or_ge pos s.size with hlt | hge
        · have h2 := htwo hlt
          omega
        · rw [hlast hge] at hle
          omega
      simp only [pikeLoop]
      split
      · rename_i stE hs
        obtain ⟨sp, hc, hle⟩ := spent_of_error hs hseed
        exact ⟨sp, hc, by omega⟩
      · rename_i stS hs
        have hspS : Spent re setup (pikeBlock re) st stS := spent_ok_id hs hseed
        obtain ⟨hb, hbd, hemp, hstk0, hown, hpool⟩ := hseeded stS hs
        split
        · obtain ⟨sp, hc, hle⟩ := hspS
          exact ⟨sp, hc, by omega⟩
        · have hroomsS := hspS.rooms
          have hmemS := hspS.held
          have hfull : unmarked (Array.replicate re.code.size false) ≤
              re.code.size := by
            have := unmarked_le_size (Array.replicate re.code.size false)
            simpa using this
          have hpayW : Charged re setup (pikeWords re) stS
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re } } :=
            Charged.pay _ hroomsS hmemS
          have hchW : Charged re setup (pikeWords re + 0) stS
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } :=
            hpayW.trans (Charged.idle
              ⟨hpayW.rooms.clist, hpayW.rooms.nlist, hpayW.rooms.stk,
                hpayW.rooms.rc, hpayW.rooms.free, hpayW.rooms.pool⟩ rfl rfl
              hpayW.held)
          have hclear : Spent re setup (closureLeftFull re + pikeWords re) stS
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } := by
            refine ⟨pikeWords re + 0, hchW, ?_⟩
            show closureLeft re (Array.replicate re.code.size false) +
              (pikeWords re + 0) ≤ closureLeft re stS.seen +
                (closureLeftFull re + pikeWords re)
            rw [closureLeft_replicate]
            omega
          have hmC : addMeasure true { stS with
              m := { stS.m with cost := stS.m.cost + pikeWords re }
              seen := Array.replicate re.code.size false } +
              stS.clist.toList.length + 1 ≤ re.code.size * 3 + 1 := by
            show stS.stk.size + stS.nlist.size +
              2 * unmarked (Array.replicate re.code.size false) +
              stS.clist.toList.length + 1 ≤ re.code.size * 3 + 1
            rw [Array.length_toList]
            omega
          have hlists : buildLive true { stS with
              m := { stS.m with cost := stS.m.cost + pikeWords re }
              seen := Array.replicate re.code.size false }
              (stS.clist.toList.map Th.h ++ mhList mh) =
              buildLive false stS (mhList mh) := by
            show handles stS.stk ++ handles stS.nlist ++
                (stS.clist.toList.map Th.h ++ mhList mh) =
              handles stS.stk ++ handles stS.clist ++ mhList mh
            rw [handles_empty hemp]
            simp [handles]
          have hstepSp := stepThreads_spent re s mo lim hwf start pos setup
            stS.clist.toList
            { stS with
              m := { stS.m with cost := stS.m.cost + pikeWords re }
              seen := Array.replicate re.code.size false }
            mh seeding matched
            ⟨by simp, hb.stk, hb.clist, hb.nlist⟩ hstk0 hb.clist
            hchW.rooms hchW.held (by rw [hlists]; exact hown)
            (by
              show stS.nlist.size + unmarked (Array.replicate re.code.size false)
                ≤ re.code.size
              omega) hmC hpool
          have hpospr : ∀ stX : PikeSt,
              Spent re setup (stS.clist.toList.length + pikeBlock re)
                { stS with
                  m := { stS.m with cost := stS.m.cost + pikeWords re }
                  seen := Array.replicate re.code.size false } stX →
              Spent re setup (pikePosition re) st stX := by
            intro stX h
            refine Spent.mono ((hspS.trans hclear).trans h) ?_
            have hcl : stS.clist.toList.length ≤ re.code.size := by
              rw [Array.length_toList]
              omega
            have hps := position_split re
            omega
          have hseenW := fun (hge : s.size ≤ pos) =>
            stepThreads_seen re s mo lim start pos hge stS.clist.toList
              { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } mh seeding matched
          split
          · rename_i stE hx
            refine hexit stE (hpospr _ (spent_of_error hx hstepSp)) ?_
            intro hge
            rw [seen_of_error hx (hseenW hge)]
            exact closureLeft_replicate re
          · rename_i out hx
            have hspO : Spent re setup (pikePosition re) st out.st :=
              hpospr _ (spent_ok_step hx hstepSp)
            have hseenO := fun (hge : s.size ≤ pos) =>
              seen_ok_step hx (hseenW hge)
            obtain ⟨o1, o2, o3⟩ := stepThreads_build re s mo lim hwf start pos
              stS.clist.toList _ mh seeding matched out hx hb.clist
              ⟨by simp, hb.stk, hb.clist, hb.nlist⟩
            obtain ⟨q1, q2, q3, q4, q5⟩ :=
              stepThreads_owned re s mo lim start pos (re.code.size * 3 + 1)
                stS.clist.toList _ mh seeding matched out hx (by simp) hstk0
                hmC (by rw [hlists]; exact hown)
            have hrec : buildMeasure { stS with
                m := { stS.m with cost := stS.m.cost + pikeWords re }
                seen := Array.replicate re.code.size false } =
                stS.clist.size + stS.nlist.size +
                  unmarked (Array.replicate re.code.size false) := rfl
            rw [hrec] at o2
            simp only [buildMeasure] at o2
            have o3' : out.st.clist.size = stS.clist.size := by rw [o3]
            have hroomsO := hspO.rooms
            have hroomsN : Rooms re { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } :=
              ⟨hroomsO.nlist, hroomsO.clist, hroomsO.stk, hroomsO.rc,
                hroomsO.free, hroomsO.pool⟩
            have hresN : ({ out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } : PikeSt).reserved =
                out.st.reserved := by
              simp only [PikeSt.reserved, thSize, regSize]
              omega
            have hspN : Spent re setup (pikePosition re) st { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } :=
              Spent.mono (hspO.trans (Spent.ofCharged
                (Charged.idle hroomsN hresN rfl hspO.held) rfl)) (by omega)
            have hfin : PosOk re { out.st with
                clist := out.st.nlist, clistCap := out.st.nlistCap
                nlist := #[], nlistCap := out.st.clistCap } out.mh := by
              refine ⟨⟨⟨o1.seenSize, o1.stk, o1.nlist, ?_⟩, rfl, ?_⟩, ?_, q1, ?_⟩
              · intro y hy
                simp at hy
              · simp only []
                omega
              · show out.st.stk.size = 0
                exact q4
              · show out.st.rc.size ≤ re.code.size * 4 + 2
                have hq : out.st.rc.size ≤
                    max stS.rc.size (re.code.size * 3 + 1 + 2) := q5
                omega
            split
            · refine hexit _ hspN ?_
              intro hge
              show closureLeft re out.st.seen = closureLeftFull re
              rw [hseenO hge]
              exact closureLeft_replicate re
            · split
              · refine hexit _ hspN ?_
                intro hge
                show closureLeft re out.st.seen = closureLeftFull re
                rw [hseenO hge]
                exact closureLeft_replicate re
              · rename_i hnot
                have hlt : pos < s.size := by
                  rename_i hge
                  simp only [Nat.not_le] at hge
                  omega
                obtain ⟨sp', hc', hle'⟩ := ih (pos + 1) _ out.mh out.seeding
                  out.matched (by omega) hfin hroomsN
                  (by rw [hresN]; exact hspO.held)
                obtain ⟨sp, hc, hle⟩ := hspN
                refine ⟨sp + sp', hc.trans hc', ?_⟩
                have hsplit : (s.size + 1 - pos) * pikePosition re =
                    pikePosition re + (s.size + 1 - (pos + 1)) * pikePosition re := by
                  have he : s.size + 1 - pos = (s.size + 1 - (pos + 1)) + 1 := by
                    omega
                  rw [he, Nat.succ_mul]
                  omega
                omega

/-! ### What a whole call spends, against its certificate

R-6 and R-8 for this configuration, at the shape a caller reads them: the
cost a lockstep run reports and the memory it peaks at are inside the
closed form of BOUNDS.md section 9, and so inside anything the checker
accepted. The run is taken at its own call shape — a context handed over
with nothing pre-reserved, which is what `{}` says — because the `3R` in the
cost line is amortized against a reservation that starts at nothing. -/

/-- R-6 for `CfgPike`: a run's cost is the setup, the delivered answer,
three times the reservation, and one position's price per starting
position. -/
theorem pikeRun_cost_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} (hwf : ReWf re) (hflag : (pikeRoom re false).2 = false) :
    (pikeRun re s start mo lim {}).usage.cost ≤
      pikeSetup re + pikeBlock re + 3 * pikeReserved re +
        pikePosition re * (s.size + 1) := by
  have hscr := pikeScratch_eq hflag
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i hstart
      simp only [Nat.not_lt] at hstart
      split
      · exact Nat.zero_le _
      · have hrooms : Rooms re ({ ({} : PikeSt) with
            clist := #[], nlist := #[], stk := #[]
            pool := #[], rc := #[], free := #[]
            seen := Array.replicate re.code.size false
            m := ⟨re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1)⟩ } : PikeSt) :=
          Rooms.zero rfl rfl rfl rfl rfl rfl
        obtain ⟨spent, hch, hle⟩ := pikeLoop_spent re s mo lim hwf start
          (re.anchored || mo.anchored) (pikeSetup re) (s.size + 2) start _
          none32 true false hstart (pikeRun_posOk re {} _) hrooms
          (by simp [PikeSt.reserved, pikeSetup, pikeBlock, pikeWords])
        rw [show pikeWords re = re.code.size / 8 + 1 from rfl] at hch
        have hres := hch.rooms.scratch_le
        have hcharge := hch.charge
        have hinit : ({ ({} : PikeSt) with
              clist := #[], nlist := #[], stk := #[]
              pool := #[], rc := #[], free := #[]
              seen := Array.replicate re.code.size false
              m := ⟨re.novec * regSize + (re.code.size / 8 + 1),
                re.novec * regSize + (re.code.size / 8 + 1),
                re.novec * regSize + (re.code.size / 8 + 1)⟩ } : PikeSt).m.cost =
              pikeSetup re ∧
            ({ ({} : PikeSt) with
              clist := #[], nlist := #[], stk := #[]
              pool := #[], rc := #[], free := #[]
              seen := Array.replicate re.code.size false
              m := ⟨re.novec * regSize + (re.code.size / 8 + 1),
                re.novec * regSize + (re.code.size / 8 + 1),
                re.novec * regSize + (re.code.size / 8 + 1)⟩ } : PikeSt).reserved
              = 0 := ⟨rfl, by simp [PikeSt.reserved]⟩
        have hseen0 : closureLeft re (Array.replicate re.code.size false) =
            closureLeftFull re := closureLeft_replicate re
        have hmul : (s.size + 1 - start) * pikePosition re ≤
            pikePosition re * (s.size + 1) := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left _ (by omega)
        rw [hinit.1, hinit.2] at hcharge
        rw [hseen0] at hle
        split
        · simp only []
          omega
        · simp only []
          omega
        · split
          · simp only []
            omega
          · simp only []
            omega

/-- R-8 for `CfgPike`: the memory a run peaks at is the setup and twice the
reservation, whatever the scan does — a number that does not move with the
subject, which is what lets a context be sized once. -/
theorem pikeRun_mem_le {re : Re} {s : ByteArray} {mo : MOpts} {lim : Limits}
    {start : Nat} (hwf : ReWf re) (hflag : (pikeRoom re false).2 = false) :
    (pikeRun re s start mo lim {}).usage.mem ≤
      pikeSetup re + pikeBlock re + 2 * pikeReserved re := by
  have hscr := pikeScratch_eq hflag
  simp only [pikeRun]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i hstart
      simp only [Nat.not_lt] at hstart
      split
      · exact Nat.zero_le _
      · have hrooms : Rooms re ({ ({} : PikeSt) with
            clist := #[], nlist := #[], stk := #[]
            pool := #[], rc := #[], free := #[]
            seen := Array.replicate re.code.size false
            m := ⟨re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1)⟩ } : PikeSt) :=
          Rooms.zero rfl rfl rfl rfl rfl rfl
        obtain ⟨spent, hch, hle⟩ := pikeLoop_spent re s mo lim hwf start
          (re.anchored || mo.anchored) (pikeSetup re) (s.size + 2) start _
          none32 true false hstart (pikeRun_posOk re {} _) hrooms
          (by simp [PikeSt.reserved, pikeSetup, pikeBlock, pikeWords])
        rw [show pikeWords re = re.code.size / 8 + 1 from rfl] at hch
        have hpeak := hch.resident
        have hscrl := hch.rooms.scratch_le
        have hpk : ({ ({} : PikeSt) with
            clist := #[], nlist := #[], stk := #[]
            pool := #[], rc := #[], free := #[]
            seen := Array.replicate re.code.size false
            m := ⟨re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1),
              re.novec * regSize + (re.code.size / 8 + 1)⟩ } : PikeSt).m.peak =
            pikeSetup re := rfl
        rw [hpk] at hpeak
        split
        · simp only []
          omega
        · simp only []
          omega
        · split
          · simp only []
            omega
          · simp only []
            omega

end Pcrevera.Ref
