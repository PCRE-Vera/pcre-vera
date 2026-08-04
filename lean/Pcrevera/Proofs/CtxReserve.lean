import Pcrevera.Ref.Context

/-!
# The creation half of R-9: a context holds exactly its bound

`ctxCreate` promises the caller one number twice over: the memory answer it
validated through `reMem` is the `memcap` it bakes in, and the arrays it
reserves — plus the words, the two result stores and the ballast — weigh
that number to the byte. The proof reads the success path the way the code
wrote it: every saturating step handed its flag back false, so each
`satAdd` and `satMul` was the exact sum or product, the held total is the
capacity sum of whichever engine's arrays got sized, and the slack tops
the total up to the accessor's value.
-/

namespace Pcrevera.Ref

open Pcrevera

/-- When `satAdd` hands its flag back false the result is the exact sum,
and the flag it was given was false already. -/
theorem satAdd_exact {a b v : Nat} {over : Bool}
    (h : satAdd a b over = (v, false)) : v = a + b ∧ over = false := by
  unfold satAdd at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2⟩

/-- The same reading of `satMul`: a false flag out means the exact product
and a false flag in. -/
theorem satMul_exact {a b v : Nat} {over : Bool}
    (h : satMul a b over = (v, false)) : v = a * b ∧ over = false := by
  unfold satMul at h
  split at h
  · rename_i hz
    simp only [Prod.mk.injEq] at h
    obtain ⟨hv, ho⟩ := h
    subst hv
    refine ⟨?_, ho⟩
    rcases hz with hz | hz <;> simp [hz]
  · split at h
    · simp at h
    · simp only [Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2⟩

/-- `satAdd_exact` in the projection form the flag chains reduce to. -/
theorem satAdd_snd {a b : Nat} {over : Bool}
    (h : (satAdd a b over).2 = false) :
    (satAdd a b over).1 = a + b ∧ over = false := by
  have hp : satAdd a b over = ((satAdd a b over).1, (satAdd a b over).2) := rfl
  rw [h] at hp
  exact satAdd_exact hp

/-- `satMul_exact` in projection form. -/
theorem satMul_snd {a b : Nat} {over : Bool}
    (h : (satMul a b over).2 = false) :
    (satMul a b over).1 = a * b ∧ over = false := by
  have hp : satMul a b over = ((satMul a b over).1, (satMul a b over).2) := rfl
  rw [h] at hp
  exact satMul_exact hp

/-- `growthCap` only threads the flag through `satMul` and `satAdd`, so a
false flag out means the flag went in false too. -/
theorem growthCap_snd {e : Nat} {over : Bool}
    (h : (growthCap e over).2 = false) : over = false := by
  unfold growthCap at h
  split at h
  · obtain ⟨-, ho⟩ := satAdd_snd h
    exact (satMul_snd ho).2
  · exact h

/-- On `pikeRoom`'s success path the reserved total is exactly the four
capacities at their entry sizes — the flag chain came back false, so the
weighted sum was never rounded. -/
theorem pikeRoom_reserved {re : Re} {room : Room} {over : Bool}
    (h : pikeRoom re over = (room, false)) :
    room.reserved = room.lists * (2 * thSize) + room.stk * thSize +
      room.tables * (2 * regSize) + room.pool * regSize := by
  simp only [pikeRoom, Prod.mk.injEq] at h
  obtain ⟨hroom, hover⟩ := h
  subst hroom
  obtain ⟨v15, f14⟩ := satAdd_snd hover
  obtain ⟨v14, f13⟩ := satMul_snd f14
  obtain ⟨v13, f12⟩ := satAdd_snd f13
  obtain ⟨v12, f11⟩ := satMul_snd f12
  obtain ⟨v11, f10⟩ := satAdd_snd f11
  obtain ⟨v10, f9⟩ := satMul_snd f10
  obtain ⟨v9, -⟩ := satMul_snd f9
  dsimp only
  rw [v15, v13, v14, v11, v12, v10, v9]

/-- The creation half of R-9 (`ctx_reserves_bound`): a context `ctxCreate`
hands back is resident for exactly its `memcap`, and that `memcap` is the
`reMem` answer the caller was given — the accessor said ok, and its value
is what the context holds, to the byte. -/
theorem ctx_resident_eq_reservation {cp : CompiledPat} {mcfg maxlen : Nat}
    {lim : Limits} {ctx : Ctx}
    (h : ctxCreate cp mcfg maxlen lim = (.ok, some ctx)) :
    ctx.resident = ctx.memcap ∧
      ctx.memcap = (reMem cp mcfg maxlen).value ∧
      (reMem cp mcfg maxlen).status = .ok := by
  simp only [ctxCreate] at h
  split at h
  · simp at h
  · simp at h
  · rename_i hst
    split at h
    · simp at h
    · rename_i picked hpick
      split at h
      · simp at h
      · rename_i nregs cbt ctrail lists stk tables pool words setup ballast heq
        split at h
        · simp at h
        · rename_i hflag
          split at h
          · simp at h
          · rename_i hheld
            split at h
            · simp at h
            · split at h
              · simp at h
              · simp only [Prod.mk.injEq, Option.some.injEq] at h
                obtain ⟨-, hctx⟩ := h
                subst hctx
                rw [Bool.not_eq_true] at hflag
                obtain ⟨vB, fA⟩ := satAdd_snd hflag
                obtain ⟨vA, -⟩ := satAdd_snd fA
                refine ⟨?_, rfl, hst⟩
                split at heq
                · split at heq
                  · simp at heq
                  · rename_i hpover
                    rw [Bool.not_eq_true] at hpover
                    simp only [Option.some.injEq, Prod.mk.injEq] at heq
                    obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, e9, e10⟩ := heq
                    subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
                    have hp : pikeRoom cp.re false =
                        ((pikeRoom cp.re false).fst, (pikeRoom cp.re false).snd) :=
                      rfl
                    rw [hpover] at hp
                    have hres := pikeRoom_reserved hp
                    simp only [Ctx.resident]
                    simp only [regSize, btSize, undoSize, thSize] at *
                    omega
                · split at heq
                  · simp at heq
                  · split at heq
                    · simp at heq
                    · rename_i hbflag
                      rw [Bool.not_eq_true] at hbflag
                      obtain ⟨vbal, f4⟩ := satAdd_snd hbflag
                      obtain ⟨vw, f3⟩ := satMul_snd f4
                      obtain ⟨vs, -⟩ := satMul_snd f3
                      simp only [Option.some.injEq, Prod.mk.injEq] at heq
                      obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, e9, e10⟩ := heq
                      subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
                      simp only [Ctx.resident]
                      simp only [regSize, btSize, undoSize, thSize] at *
                      omega

end Pcrevera.Ref
