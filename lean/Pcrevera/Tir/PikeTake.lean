import Pcrevera.Tir.RegionKids
import Pcrevera.Ref.Pike

/-!
# The call-composition sample: `pike_take`, conditionally (gate 5 scouting)

The stratification report picked this function by its recorded rule: the
smallest owed function that calls a callee from inside a loop — the
fuel-through-iteration pattern gate 4 could not price — with composition
exercised at more than one site. Its layer R counterpart is `Ref.pikeTake`,
and its one distinct callee is `charge_grow`, `Ref.chargeGrow`.

What is proved here is *conditional*: `pike_take` simulates `Ref.pikeTake`
given a simulation contract for `charge_grow`, stated in `ChargeGrowSim`
below as the `Runs` lemma the campaign will owe that function anyway. The
coverage ledger does not count this theorem — a conditional lemma counts
only when every callee premise is discharged — and the point of proving it
is the number it produces: what caller-side composition costs, separate
from the callee's own proof.

The contract's premises are where both sides' arithmetic honestly meets.
TIR counters saturate at `counterMax` and its `u32` multiply wraps, while
layer R computes in `Nat`; the checks-before-commit discipline means the
two agree exactly when the capacities in play leave the saturation point
unreachable — `2 * (maxv * esize) ≤ counterMax`, `maxv ≤ ceiling` — and
both call sites here sit far below those lines.
-/

namespace Pcrevera.Tir

open Pcrevera.Ref (Meter Limits chargeGrow pikeTake PikeSt)

/-- The body on its own, so that a proof can unfold it to a list of
statements and step down it. -/
def pikeTakeBody : List Stmt :=
    [
      .ifS (.cmp .gt (.len (.var "free")) (.litInt .u32 0))
        [.letS "tmp1" (.int .u32) (some (.litInt .u32 0)),
         .pop (.var "free") (.var "tmp1"),
         .assign (.index (.var "rc") (.var "tmp1")) (.litInt .u32 1),
         .returnS (some (.var "tmp1"))]
        [],
      .letS "tmp2" (.int .u32) (some (.len (.var "rc"))),
      .ifS (.cmp .ge (.var "tmp2") (.litInt .u32 262796))
        [.returnS (some (.litInt .u32 4294967295))]
        [],
      .letS "tmp3" .bool (some (.litBool false)),
      .call "charge_grow"
        [.inArg (.cap (.var "rc")), .inArg (.len (.var "rc")),
         .inArg (.litInt .u32 4), .inArg (.litInt .u32 262796),
         .inoutArg (.var "mem"), .inoutArg (.var "peak"),
         .inoutArg (.var "cost"),
         .inArg (.var "memlimit"), .inArg (.var "costlimit")]
        (some (.var "tmp3")),
      .ifS (.un .not (.var "tmp3"))
        [.returnS (some (.litInt .u32 4294967295))]
        [],
      .push (.var "rc") (.litInt .u32 1),
      .letS "tmp4" (.int .u32) (some (.litInt .u32 0)),
      .whileS (.cmp .lt (.var "tmp4") (.var "novec"))
        (.bin .sub (.cast (.int .counter) (.var "novec"))
          (.cast (.int .counter) (.var "tmp4")))
        [.call "charge_grow"
          [.inArg (.cap (.var "pool")), .inArg (.len (.var "pool")),
           .inArg (.litInt .u32 4), .inArg (.litInt .u32 134549508),
           .inoutArg (.var "mem"), .inoutArg (.var "peak"),
           .inoutArg (.var "cost"),
           .inArg (.var "memlimit"), .inArg (.var "costlimit")]
          (some (.var "tmp3")),
         .ifS (.un .not (.var "tmp3"))
           [.returnS (some (.litInt .u32 4294967295))]
           [],
         .push (.var "pool") (.litInt .u32 4294967295),
         .assign (.var "tmp4") (.bin .add (.var "tmp4") (.litInt .u32 1))],
      .returnS (some (.var "tmp2"))]

/-- `pike_take` as a term the kernel can reduce, held to the artifact by
the guard below, exactly as `regionKidsFunc` is. -/
def pikeTakeFunc : Func :=
  { name := "pike_take"
    params := [⟨"pool", .vec (.int .u32) 134549508, true⟩,
               ⟨"rc", .vec (.int .u32) 262796, true⟩,
               ⟨"free", .vec (.int .u32) 262796, true⟩,
               ⟨"novec", .int .u32, false⟩,
               ⟨"mem", .int .counter, true⟩,
               ⟨"peak", .int .counter, true⟩,
               ⟨"cost", .int .counter, true⟩,
               ⟨"memlimit", .int .counter, false⟩,
               ⟨"costlimit", .int .counter, false⟩]
    ret := some (.int .u32)
    body := pikeTakeBody }

theorem pikeTakeFunc_body : pikeTakeFunc.body = pikeTakeBody := rfl

/-- The parameter row on its own, so that reading the outs back does not
drag the body through `simp` with it. -/
theorem pikeTakeFunc_params :
    pikeTakeFunc.params =
      [⟨"pool", .vec (.int .u32) 134549508, true⟩,
       ⟨"rc", .vec (.int .u32) 262796, true⟩,
       ⟨"free", .vec (.int .u32) 262796, true⟩,
       ⟨"novec", .int .u32, false⟩,
       ⟨"mem", .int .counter, true⟩,
       ⟨"peak", .int .counter, true⟩,
       ⟨"cost", .int .counter, true⟩,
       ⟨"memlimit", .int .counter, false⟩,
       ⟨"costlimit", .int .counter, false⟩] := rfl

private def artifactFunc (name : String) : Option Func :=
  match artifact with
  | .ok p => p.func? name
  | .error _ => none

-- The transcription is the artifact's function, byte for byte through the
-- decoder, or the build stops here.
#guard artifactFunc "pike_take" == some pikeTakeFunc

/-- The callee's parameter row, which is all the caller's side of a call
reads: the argument evaluation and the write-back walk it. The body stays
the callee lemma's business. -/
def chargeGrowParams : List Param :=
  [⟨"oldcap", .int .u32, false⟩, ⟨"lenv", .int .u32, false⟩,
   ⟨"esize", .int .u32, false⟩, ⟨"maxv", .int .u32, false⟩,
   ⟨"mem", .int .counter, true⟩, ⟨"peak", .int .counter, true⟩,
   ⟨"cost", .int .counter, true⟩,
   ⟨"memlimit", .int .counter, false⟩, ⟨"costlimit", .int .counter, false⟩]

#guard (artifactFunc "charge_grow").map Func.params == some chargeGrowParams

/-! ## The callee's contract

What the campaign will owe `charge_grow` anyway, quoted here as the
hypothesis the conditional theorem composes with. The bounds are where the
two arithmetics honestly meet — TIR saturates its counters and wraps its
`u32` multiply where layer R computes in `Nat`, and the checks-before-
commit discipline makes the two agree exactly while the capacities keep
every intermediate below both lines. Both call sites in `pike_take` sit
far below them. -/

/-- How one meter and one limit pair arrive at `charge_grow`. -/
def cgArgs (oldcap lenv esize maxv : Nat) (m : Meter) (lim : Limits) :
    List Value :=
  [markVal oldcap, markVal lenv, markVal esize, markVal maxv,
   markVal m.mem, markVal m.peak, markVal m.cost,
   markVal lim.mem, markVal lim.cost]

/-- And how they leave: the four sizes and the two limits unchanged, the
meter wherever the charge left it. -/
def cgOuts (oldcap lenv esize maxv : Nat) (m : Meter) (lim : Limits) :
    List Value :=
  [markVal oldcap, markVal lenv, markVal esize, markVal maxv,
   markVal m.mem, markVal m.peak, markVal m.cost,
   markVal lim.mem, markVal lim.cost]

def ChargeGrowSim (p : Program) : Prop :=
  ∀ (oldcap lenv esize maxv : Nat) (m : Meter) (lim : Limits),
    oldcap ≤ maxv → 1 ≤ esize → maxv < 2147483648 →
    2 * (maxv * esize) ≤ 9007199254740991 →
    lim.mem ≤ 9007199254740991 → lim.cost ≤ 9007199254740991 →
    match chargeGrow oldcap lenv esize maxv m lim with
    | some (m', _) =>
        Runs p "charge_grow" (cgArgs oldcap lenv esize maxv m lim)
          (cgOuts oldcap lenv esize maxv m' lim, some (.bool true))
    | none =>
        Runs p "charge_grow" (cgArgs oldcap lenv esize maxv m lim)
          (cgOuts oldcap lenv esize maxv m lim, some (.bool false))

/-- The contract, run against the artifact rather than assumed of it: the
decoded `charge_grow` answers what `ChargeGrowSim` says on one input per
outcome the function has. A conditional theorem is only worth having if
its hypothesis is true, and these are the cheap evidence rather than the
proof of it — the lemma that replaces them is gate 5's, and it is what
makes this theorem unconditional. -/
private def cgAgrees (oldcap len esize maxv : Nat) (m : Meter)
    (lim : Limits) : Bool :=
  match artifact with
  | .error _ => false
  | .ok p =>
      match callFunc 8 p "charge_grow" (cgArgs oldcap len esize maxv m lim) with
      | some (.ok (outs, some (.bool b))) =>
          match chargeGrow oldcap len esize maxv m lim with
          | some (m', _) => b && outs == cgOuts oldcap len esize maxv m' lim
          | none => !b && outs == cgOuts oldcap len esize maxv m lim
      | _ => false

-- Room already reserved: nothing charged, the capacity stands.
#guard cgAgrees 8 4 4 262796 ⟨0, 0, 0⟩ ⟨1000, 0, 1000⟩

-- The reservation is full and the growth fits.
#guard cgAgrees 0 0 4 262796 ⟨0, 0, 0⟩ ⟨1000, 0, 1000⟩
#guard cgAgrees 4 4 4 262796 ⟨100, 0, 100⟩ ⟨100000, 0, 100000⟩

-- Refused for memory, then refused for cost. `Limits` is cost, stack,
-- memory in that order, so the tight field is the third then the first.
#guard cgAgrees 4 4 4 262796 ⟨0, 0, 0⟩ ⟨100000, 0, 8⟩
#guard cgAgrees 4 4 4 262796 ⟨0, 0, 0⟩ ⟨8, 0, 100000⟩

-- And refused at the declared maximum.
#guard cgAgrees 262796 262796 4 262796 ⟨0, 0, 0⟩ ⟨1000000, 0, 1000000⟩

-- The pool site's own width, which is the other call this file makes.
#guard cgAgrees 0 0 4 134549508 ⟨0, 0, 0⟩ ⟨1000, 0, 1000⟩

/-- The contract's out list never hides a lost name. `charge_grow`'s three
`inout` parameters are the meter's counters, so the outs `OutsPresent` asks
about are integers and never the `false` that `outsOf` also answers for a
name the callee dropped. Settled once for all six callers rather than at
each call site. -/
theorem cgOuts_present {oldcap lenv esize maxv : Nat} {m : Meter}
    {lim : Limits} :
    OutsPresent chargeGrowParams (cgOuts oldcap lenv esize maxv m lim) := by
  simp [OutsPresent, chargeGrowParams, cgOuts, markVal]

/-- What a successful growth charge says about the capacity it answers,
which is the whole of what a caller's push needs to know about the callee.
The reservation discipline lives or dies here: TIR's `grown` and layer R's
growth schedule have to name the same number, and this is where they are
made to. -/
theorem chargeGrow_cap {oldcap len esize maxv : Nat} {m m' : Meter}
    {lim : Limits} {cap' : Nat} (hle : len ≤ oldcap) (hmax : oldcap ≤ maxv)
    (h : chargeGrow oldcap len esize maxv m lim = some (m', cap')) :
    len < maxv ∧ len < cap' ∧ cap' ≤ maxv ∧
      (if len = oldcap then grown maxv oldcap else oldcap) = cap' := by
  have hsched : grown maxv oldcap
      = min maxv (max Pcrevera.Ref.growMin
          (oldcap * Pcrevera.Ref.growFactor)) := by
    show min maxv (max 4 (2 * oldcap)) = _
    simp only [Pcrevera.Ref.growMin, Pcrevera.Ref.growFactor, Nat.mul_comm]
  by_cases hlt : len < oldcap
  · -- Room already reserved: nothing is charged and the capacity stands.
    have hkeep : cap' = oldcap := by
      unfold chargeGrow at h
      rw [if_pos hlt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    rw [if_neg (by omega), hkeep]
    exact ⟨by omega, by omega, by omega, rfl⟩
  · -- The reservation is full, so the schedule decides the new capacity.
    have hlen : len = oldcap := by omega
    have hroom : len < maxv := by
      rcases Nat.lt_or_ge len maxv with hh | hh
      · exact hh
      · exfalso
        unfold chargeGrow at h
        rw [if_neg hlt, if_pos hh] at h
        exact absurd h (by simp)
    have hcap : cap' = min maxv (max Pcrevera.Ref.growMin
        (oldcap * Pcrevera.Ref.growFactor)) := by
      unfold chargeGrow at h
      rw [if_neg hlt, if_neg (by omega : ¬len ≥ maxv)] at h
      simp only [] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
    rw [if_pos hlen, hsched, hcap]
    simp only [Pcrevera.Ref.growMin, Pcrevera.Ref.growFactor]
    exact ⟨by omega, by omega, by omega, by trivial⟩

/-! ## The fill loop, against `pikeTake.fill` -/

/-- How a Pike pool word is spelled as a TIR value. -/
def u32Val (u : UInt32) : Value := .int (Int.ofNat u.toNat)

def takeCond : Expr := .cmp .lt (.var "tmp4") (.var "novec")

def takeBody : List Stmt :=
  [.call "charge_grow"
    [.inArg (.cap (.var "pool")), .inArg (.len (.var "pool")),
     .inArg (.litInt .u32 4), .inArg (.litInt .u32 134549508),
     .inoutArg (.var "mem"), .inoutArg (.var "peak"),
     .inoutArg (.var "cost"),
     .inArg (.var "memlimit"), .inArg (.var "costlimit")]
    (some (.var "tmp3")),
   .ifS (.un .not (.var "tmp3"))
     [.returnS (some (.litInt .u32 4294967295))]
     [],
   .push (.var "pool") (.litInt .u32 4294967295),
   .assign (.var "tmp4") (.bin .add (.var "tmp4") (.litInt .u32 1))]

theorem takeBody_eq :
    pikeTakeFunc.body[8]? = some (.whileS takeCond
      (.bin .sub (.cast (.int .counter) (.var "novec"))
        (.cast (.int .counter) (.var "tmp4"))) takeBody) := rfl

/-- Between rounds of the fill loop: `tmp4` counts the pushes, the pool and
the meter are wherever layer R says, and everything else stands still. The
pool's capacity is exact rather than existential, because the reservation
discipline is the thing under test: layer R tracks it, and the two growth
rules have to agree or the proof stops. -/
structure FillSt (env : Env) (st : PikeSt) (rcv freev t2 : Value)
    (novec i : Nat) (lim : Limits) : Prop where
  tmp4 : env.get "tmp4" = some ⟨.int .u32, markVal i⟩
  tmp3 : ∃ b, env.get "tmp3" = some ⟨.bool, .bool b⟩
  nov : env.get "novec" = some ⟨.int .u32, markVal novec⟩
  pool : env.get "pool" = some ⟨.vec (.int .u32) 134549508,
    .seq 134549508 (st.pool.toList.map u32Val) st.poolCap⟩
  rc : env.get "rc" = some ⟨.vec (.int .u32) 262796, rcv⟩
  free : env.get "free" = some ⟨.vec (.int .u32) 262796, freev⟩
  tmp2 : env.get "tmp2" = some ⟨.int .u32, t2⟩
  mem : env.get "mem" = some ⟨.int .counter, markVal st.m.mem⟩
  peak : env.get "peak" = some ⟨.int .counter, markVal st.m.peak⟩
  cost : env.get "cost" = some ⟨.int .counter, markVal st.m.cost⟩
  meml : env.get "memlimit" = some ⟨.int .counter, markVal lim.mem⟩
  costl : env.get "costlimit" = some ⟨.int .counter, markVal lim.cost⟩

/-- The loop leaves behind exactly what `pikeTake.fill` computes: every
round is one unfolding of the fuel, a refused charge is the early return,
and the budget the callee spends each round stays behind the existential.

This lemma is the measurement the sample exists to take, and the section 10
automation is what it now reads through: one `evalStmt_call_outs` per call
site instead of a write-back walked component by component, and one `store`
per store fact. -/
theorem fillLoop {p : Program} {cg : Func}
    (hcg : ChargeGrowSim p)
    (hcgf : p.func? "charge_grow" = some cg)
    (hcgp : cg.params = chargeGrowParams)
    {lim : Limits} (hmem : lim.mem ≤ 9007199254740991)
    (hcost : lim.cost ≤ 9007199254740991)
    {novec : Nat} (hnovec : novec < 4294967296) :
    ∀ (k i : Nat) (st : PikeSt) (env : Env) (rcv freev t2 : Value),
      i + k = novec →
      st.pool.size ≤ st.poolCap → st.poolCap ≤ 134549508 →
      FillSt env st rcv freev t2 novec i lim →
      (match pikeTake.fill lim k st with
       | .ok st' => ∃ n env',
           evalWhile n p takeCond takeBody env = some (.ok (env', .normal))
           ∧ ∃ i', FillSt env' st' rcv freev t2 novec i' lim
       | .error st' => ∃ n env',
           evalWhile n p takeCond takeBody env
             = some (.ok (env', .ret (some (.int 4294967295))))
           ∧ ∃ i', FillSt env' st' rcv freev t2 novec i' lim) := by
  intro k
  induction k with
  | zero =>
      intro i st env rcv freev t2 hk hsz hcap hst
      have hc : evalExpr p env takeCond = .ok (.bool false) := by
        show evalExpr p env (.cmp .lt (.var "tmp4") (.var "novec")) = _
        rw [evalExpr_cmp (evalExpr_var hst.tmp4) (evalExpr_var hst.nov)]
        show Res.ok (Value.bool (decide ((i : Int) < (novec : Int)))) = _
        rw [decide_eq_false (by omega)]
      simp only [pikeTake.fill]
      exact ⟨1, env, evalWhile_done hc, i, hst⟩
  | succ k ih =>
      intro i st env rcv freev t2 hk hsz hcap hst
      obtain ⟨b0, htmp3⟩ := hst.tmp3
      -- The condition says go round.
      have hc : evalExpr p env takeCond = .ok (.bool true) := by
        show evalExpr p env (.cmp .lt (.var "tmp4") (.var "novec")) = _
        rw [evalExpr_cmp (evalExpr_var hst.tmp4) (evalExpr_var hst.nov)]
        show Res.ok (Value.bool (decide ((i : Int) < (novec : Int)))) = _
        rw [decide_eq_true (by omega)]
      -- The arguments of the charge, off the store as it stands.
      have hargs : evalArgs p env cg.params
          [.inArg (.cap (.var "pool")), .inArg (.len (.var "pool")),
           .inArg (.litInt .u32 4), .inArg (.litInt .u32 134549508),
           .inoutArg (.var "mem"), .inoutArg (.var "peak"),
           .inoutArg (.var "cost"),
           .inArg (.var "memlimit"), .inArg (.var "costlimit")]
          = .ok (cgArgs st.poolCap st.pool.size 4 134549508 st.m lim) := by
        rw [hcgp]
        simp only [chargeGrowParams, evalArgs,
          evalExpr_cap (evalExpr_var hst.pool),
          evalExpr_len (evalExpr_var hst.pool),
          evalExpr_lit, readPlace_var hst.mem, readPlace_var hst.peak,
          readPlace_var hst.cost, evalExpr_var hst.meml,
          evalExpr_var hst.costl, Res.ok_bind]
        simp [cgArgs, markVal]
      have hrun := hcg st.poolCap st.pool.size Pcrevera.Ref.regSize
        Pcrevera.Ref.maxPool st.m lim hcap (by decide) (by decide)
        (by decide) hmem hcost
      have hml : (st.pool.toList.map u32Val).length = st.pool.size := by simp
      have hpm : Pcrevera.Ref.maxPool = 134549508 := by decide
      match hgrow : chargeGrow st.poolCap st.pool.size Pcrevera.Ref.regSize
          Pcrevera.Ref.maxPool st.m lim with
      | some (m', newcap) =>
          rw [hgrow] at hrun
          obtain ⟨env4, henv4⟩ : ∃ e : Env,
              ((((env.set "mem" (markVal m'.mem)).set "peak"
                (markVal m'.peak)).set "cost" (markVal m'.cost)).set "tmp3"
                (.bool true)) = e := ⟨_, rfl⟩
          obtain ⟨nc, hcall⟩ := evalStmt_call_outs (dest := some (.var "tmp3"))
            hcgf hargs hrun (hcgp ▸ cgOuts_present)
          store [hcgp, chargeGrowParams, writeOuts, cgOuts, hst.mem, hst.peak,
            hst.cost, htmp3, henv4] at hcall
          have h4tmp3 : env4.get "tmp3" = some ⟨.bool, .bool true⟩ := by
            store [← henv4, htmp3]
          have h4pool : env4.get "pool" = some ⟨.vec (.int .u32) 134549508,
              .seq 134549508 (st.pool.toList.map u32Val) st.poolCap⟩ := by
            store [← henv4, hst.pool]
          -- The push stays under the declared maximum, because the charge
          -- that succeeded said so — and the two growth rules agree on the
          -- new capacity, which is the reservation discipline under test.
          have hgrown := chargeGrow_cap hsz (by rw [hpm]; exact hcap) hgrow
          rw [hpm] at hgrown
          obtain ⟨env5, henv5⟩ : ∃ e : Env, env4.set "pool"
              (.seq 134549508
                ((st.pool.push Pcrevera.unset32).toList.map u32Val)
                newcap) = e := ⟨_, rfl⟩
          have h5tmp4 : env5.get "tmp4" = some ⟨.int .u32, markVal i⟩ := by
            store [← henv5, ← henv4, hst.tmp4]
          obtain ⟨env6, henv6⟩ : ∃ e : Env,
              env5.set "tmp4" (.int (i + 1 : Nat)) = e := ⟨_, rfl⟩
          have hbody : ∀ f, evalStmts (max nc f) p takeBody env
              = some (.ok (env6, .normal)) := fun f => by
            unfold takeBody
            rw [evalStmts_cons (evalStmt_mono hcall (Nat.le_max_left _ _)),
              evalStmts_cons (show evalStmt (max nc f) p
                  (.ifS (.un .not (.var "tmp3"))
                    [.returnS (some (.litInt .u32 4294967295))] []) env4
                  = some (.ok (env4, .normal)) by
                rw [evalStmt_if_false (evalExpr_not (b := true)
                  (evalExpr_var h4tmp3)), evalStmts_nil]),
              evalStmts_cons (evalStmt_push_var h4pool
                (evalExpr_lit (t := .u32) (v := 4294967295))
                (by rw [hml]; exact hgrown.1)),
              show (if (st.pool.toList.map u32Val).length = st.poolCap
                  then grown 134549508 st.poolCap else st.poolCap) = newcap by
                rw [hml]; exact hgrown.2.2.2,
              show st.pool.toList.map u32Val ++ [Value.int 4294967295]
                  = (st.pool.push Pcrevera.unset32).toList.map u32Val by
                simp [u32Val, Pcrevera.unset32],
              henv5,
              evalStmts_cons (evalStmt_assign_var (t := .int .u32)
                (cur := markVal i) h5tmp4
                (evalExpr_addOne (k := i) (by omega) h5tmp4)),
              henv6, evalStmts_nil]
          -- The store after the round satisfies the invariant at `i + 1`,
          -- against the state layer R recurses with.
          obtain ⟨st1, hst1⟩ : ∃ s : PikeSt, ({ st with m := m', poolCap := newcap, pool := st.pool.push Pcrevera.unset32 } : PikeSt) = s := ⟨_, rfl⟩
          have hst6 : FillSt env6 st1 rcv freev t2 novec (i + 1) lim := by
            rw [← hst1]
            refine ⟨?_, ⟨true, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              store [← henv6, ← henv5, ← henv4, markVal, hst.tmp4, htmp3,
                hst.nov, hst.pool, hst.rc, hst.free, hst.tmp2, hst.mem,
                hst.peak, hst.cost, hst.meml, hst.costl] <;> rfl
          have hih := ih (i + 1) st1 env6 rcv freev t2 (by omega)
            (by rw [← hst1]
                have hlt' := hgrown.2.1
                simp only [Array.size_push]
                omega)
            (by rw [← hst1]; exact hgrown.2.2.1) hst6
          -- One unfolding of the fuel, and the round is the recursion.
          simp only [pikeTake.fill]
          rw [hgrow]
          simp only []
          rw [hst1]
          match hfill : pikeTake.fill lim k st1 with
          | .ok st2 =>
              rw [hfill] at hih
              obtain ⟨n, env', hrun, hinv⟩ := hih
              exact ⟨max nc n + 1, env', by
                rw [evalWhile_step hc (hbody n)]
                exact evalWhile_mono hrun (Nat.le_max_right _ _), hinv⟩
          | .error st2 =>
              rw [hfill] at hih
              obtain ⟨n, env', hrun, hinv⟩ := hih
              exact ⟨max nc n + 1, env', by
                rw [evalWhile_step hc (hbody n)]
                exact evalWhile_mono hrun (Nat.le_max_right _ _), hinv⟩
      | none =>
          rw [hgrow] at hrun
          obtain ⟨env4, henv4⟩ : ∃ e : Env,
              ((((env.set "mem" (markVal st.m.mem)).set "peak"
                (markVal st.m.peak)).set "cost" (markVal st.m.cost)).set "tmp3"
                (.bool false)) = e := ⟨_, rfl⟩
          obtain ⟨nc, hcall⟩ := evalStmt_call_outs (dest := some (.var "tmp3"))
            hcgf hargs hrun (hcgp ▸ cgOuts_present)
          store [hcgp, chargeGrowParams, writeOuts, cgOuts, hst.mem, hst.peak,
            hst.cost, htmp3, henv4] at hcall
          have h4tmp3 : env4.get "tmp3" = some ⟨.bool, .bool false⟩ := by
            store [← henv4, htmp3]
          -- The refused charge is the early return, climbing out of the
          -- loop with the store exactly as the charges left it.
          have hbody : evalStmts nc p takeBody env
              = some (.ok (env4, .ret (some (.int 4294967295)))) := by
            unfold takeBody
            rw [evalStmts_cons hcall]
            refine evalStmts_cons_abrupt (by simp) ?_
            rw [evalStmt_if_true (evalExpr_not (b := false)
                (evalExpr_var h4tmp3)),
              evalStmts_cons_abrupt (by simp)
                (evalStmt_return_some
                  (evalExpr_lit (t := .u32) (v := 4294967295)))]
          simp only [pikeTake.fill]
          rw [hgrow]
          refine ⟨nc + 1, env4, evalWhile_return hc hbody, i, ?_, ⟨false, ?_⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            store [← henv4, hst.tmp4, htmp3, hst.nov, hst.pool, hst.rc,
              hst.free, hst.tmp2, hst.mem, hst.peak, hst.cost, hst.meml,
              hst.costl]

/-! ## The theorem: `pike_take` against `Ref.pikeTake`, conditionally -/

/-- How the nine parameters arrive, and how they leave: the same relation
serves both directions because the sizes and limits never move. -/
def takeArgs (st : PikeSt) (novec : Nat) (lim : Limits) : List Value :=
  [.seq 134549508 (st.pool.toList.map u32Val) st.poolCap,
   .seq 262796 (st.rc.toList.map markVal) st.rcCap,
   .seq 262796 (st.free.toList.map markVal) st.freeCap,
   markVal novec, markVal st.m.mem, markVal st.m.peak, markVal st.m.cost,
   markVal lim.mem, markVal lim.cost]

/-- The back of a nonempty array, spelled as the element it is. -/
theorem back!_eq_getElem {α : Type} [Inhabited α] {A : Array α}
    (h : 0 < A.size) : A.back! = A[A.size - 1]'(by omega) := by
  rw [Array.back!_eq_back?, Array.back?_eq_getElem?,
    Array.getElem?_eq_getElem (by omega)]
  rfl

/-- The last of a mark array, read off the mapped list. -/
theorem getLast?_toList_map {A : Array Nat} (h : 0 < A.size) :
    (A.toList.map markVal).getLast? = some (markVal A.back!) := by
  rw [List.getLast?_map, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by simp only [Array.length_toList]; omega)]
  simp only [Option.map_some, Option.some.injEq, Array.length_toList,
    Array.getElem_toList]
  rw [back!_eq_getElem h]

/-- Dropping the last commutes with the spelling. -/
theorem dropLast_toList_map {A : Array Nat} :
    (A.toList.map markVal).dropLast = A.pop.toList.map markVal := by
  rw [Array.toList_pop, List.map_dropLast]

/-- The fill loop touches the pool and the meter and nothing else: the
frame fact the final read-out leans on. -/
theorem fill_frame {lim : Limits} : ∀ (k : Nat) (st st' : PikeSt),
    (pikeTake.fill lim k st = .ok st' ∨ pikeTake.fill lim k st = .error st') →
    st'.rc = st.rc ∧ st'.rcCap = st.rcCap ∧ st'.free = st.free ∧
      st'.freeCap = st.freeCap := by
  intro k
  induction k with
  | zero =>
      intro st st' h
      simp only [pikeTake.fill] at h
      rcases h with h | h
      · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
      · cases h
  | succ k ih =>
      intro st st' h
      simp only [pikeTake.fill] at h
      cases hg : chargeGrow st.poolCap st.pool.size Pcrevera.Ref.regSize
          Pcrevera.Ref.maxPool st.m lim with
      | none =>
          rw [hg] at h
          rcases h with h | h
          · cases h
          · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
      | some pr =>
          obtain ⟨m1, cap1⟩ := pr
          rw [hg] at h
          simp only [] at h
          have hrest := ih _ st' h
          exact hrest

/-- `pike_take` simulates `Ref.pikeTake`, conditionally on the `charge_grow`
contract: from a related pool, block table, free list and meter, the two
sides agree on the handle or agree on the refusal, and the store lands
where layer R says — partial charges kept, exactly as `POut` keeps them.

The premises: the reservation invariants (`size ≤ cap ≤ max`) that every
Pike context maintains, the free list holding real handles, and the limit
bounds `Limits.valid` guarantees. None is new to this function; all of
them are what the context machinery already promises. -/
theorem pike_take_simulates {p : Program} {cg : Func}
    (hcg : ChargeGrowSim p)
    (hcgf : p.func? "charge_grow" = some cg)
    (hcgp : cg.params = chargeGrowParams)
    (hf : p.func? "pike_take" = some pikeTakeFunc)
    {st : PikeSt} {novec : Nat} {lim : Limits}
    (hnovec : novec < 4294967296)
    (hpool : st.pool.size ≤ st.poolCap) (hpcap : st.poolCap ≤ 134549508)
    (hrc : st.rc.size ≤ st.rcCap) (hrcap : st.rcCap ≤ 262796)
    (hfree : ∀ x ∈ st.free, x < st.rc.size)
    (hmem : lim.mem ≤ 9007199254740991)
    (hcost : lim.cost ≤ 9007199254740991) :
    match pikeTake st novec lim with
    | .ok (st', h) =>
        Runs p "pike_take" (takeArgs st novec lim)
          (takeArgs st' novec lim, some (markVal h))
    | .error st' =>
        Runs p "pike_take" (takeArgs st novec lim)
          (takeArgs st' novec lim, some (.int 4294967295)) := by
  obtain ⟨env0, henv0⟩ : ∃ e : Env,
      bindParams pikeTakeFunc.params (takeArgs st novec lim) = e := ⟨_, rfl⟩
  have h0pool : env0.get "pool" = some ⟨.vec (.int .u32) 134549508,
      .seq 134549508 (st.pool.toList.map u32Val) st.poolCap⟩ := by
    rw [← henv0]; rfl
  have h0rc : env0.get "rc" = some ⟨.vec (.int .u32) 262796,
      .seq 262796 (st.rc.toList.map markVal) st.rcCap⟩ := by
    rw [← henv0]; rfl
  have h0free : env0.get "free" = some ⟨.vec (.int .u32) 262796,
      .seq 262796 (st.free.toList.map markVal) st.freeCap⟩ := by
    rw [← henv0]; rfl
  have h0nov : env0.get "novec"
      = some ⟨.int .u32, markVal novec⟩ := by rw [← henv0]; rfl
  have h0mem : env0.get "mem"
      = some ⟨.int .counter, markVal st.m.mem⟩ := by rw [← henv0]; rfl
  have h0peak : env0.get "peak"
      = some ⟨.int .counter, markVal st.m.peak⟩ := by rw [← henv0]; rfl
  have h0cost : env0.get "cost"
      = some ⟨.int .counter, markVal st.m.cost⟩ := by rw [← henv0]; rfl
  have h0meml : env0.get "memlimit"
      = some ⟨.int .counter, markVal lim.mem⟩ := by rw [← henv0]; rfl
  have h0costl : env0.get "costlimit"
      = some ⟨.int .counter, markVal lim.cost⟩ := by rw [← henv0]; rfl
  by_cases hpos : 0 < st.free.size
  · -- The free list has a block: pop it, mark one reference, hand it back.
    obtain ⟨stF, hstF⟩ : ∃ s : PikeSt, ({ st with free := st.free.pop, rc := st.rc.set! st.free.back! 1 } : PikeSt) = s := ⟨_, rfl⟩
    have hback : st.free.back! < st.rc.size := by
      refine hfree _ ?_
      rw [back!_eq_getElem hpos]
      exact Array.getElem_mem _
    have hc1 : evalExpr p env0
        (.cmp .gt (.len (.var "free")) (.litInt .u32 0))
        = .ok (.bool true) := by
      rw [evalExpr_cmp (evalExpr_len (evalExpr_var h0free))
        (evalExpr_lit (t := .u32) (v := 0))]
      show Res.ok (Value.bool
        (decide (((st.free.toList.map markVal).length : Int) > 0))) = _
      rw [decide_eq_true (by simp only [List.length_map,
        Array.length_toList]; omega)]
    obtain ⟨env1, henv1⟩ : ∃ e : Env,
        env0.declare "tmp1" (.int .u32) (.int 0) = e := ⟨_, rfl⟩
    obtain ⟨env2, henv2⟩ : ∃ e : Env,
        (env1.set "free" (.seq 262796 (st.free.pop.toList.map markVal)
          st.freeCap)).set "tmp1" (markVal st.free.back!) = e := ⟨_, rfl⟩
    obtain ⟨env3, henv3⟩ : ∃ e : Env, env2.set "rc"
        (.seq 262796 ((st.rc.set! st.free.back! 1).toList.map markVal)
          st.rcCap) = e := ⟨_, rfl⟩
    have h1free : env1.get "free" = some ⟨.vec (.int .u32) 262796,
        .seq 262796 (st.free.toList.map markVal) st.freeCap⟩ := by
      store [← henv1, h0free]
    have h1tmp1 : env1.get "tmp1" = some ⟨.int .u32, .int 0⟩ := by
      store [← henv1]
    have h2rc : env2.get "rc" = some ⟨.vec (.int .u32) 262796,
        .seq 262796 (st.rc.toList.map markVal) st.rcCap⟩ := by
      store [← henv2, ← henv1, h0rc]
    have h2tmp1 : env2.get "tmp1"
        = some ⟨.int .u32, markVal st.free.back!⟩ := by
      store [← henv2, h1tmp1]
    have h3tmp1 : env3.get "tmp1"
        = some ⟨.int .u32, markVal st.free.back!⟩ := by
      store [← henv3, h2tmp1]
    have hbody : ∀ f, evalStmts f p pikeTakeFunc.body env0
        = some (.ok (env3, .ret (some (markVal st.free.back!)))) := by
      intro f
      rw [pikeTakeFunc_body]
      unfold pikeTakeBody
      refine evalStmts_cons_abrupt (by simp) ?_
      rw [evalStmt_if_true hc1,
        evalStmts_cons (evalStmt_let (evalExpr_lit (t := .u32) (v := 0))),
        henv1,
        evalStmts_cons (evalStmt_pop_var (by decide) h1free h1tmp1
          (getLast?_toList_map hpos)),
        dropLast_toList_map, henv2,
        evalStmts_cons (evalStmt_assign_index_var h2rc (evalExpr_var h2tmp1)
          (by simp only [List.length_map, Array.length_toList]; omega)
          (evalExpr_lit (t := .u32) (v := 1))),
        show (Value.int 1) = markVal 1 from rfl, ← toList_map_set!, henv3,
        evalStmts_cons_abrupt (by simp)
          (evalStmt_return_some (evalExpr_var h3tmp1))]
    have hruns := runs_of_body hf (inner := env3)
      (flow := .ret (some (markVal st.free.back!)))
      ⟨1, by rw [henv0]; exact hbody 1⟩
    have houts : outsOf pikeTakeFunc.params env3
        = takeArgs stF novec lim := by
      store [outsOf, pikeTakeFunc_params, takeArgs, List.map_cons,
        List.map_nil, ← hstF, ← henv3, ← henv2, ← henv1, h0pool, h0rc,
        h0free, h0nov, h0mem, h0peak, h0cost, h0meml, h0costl]
    have hred : pikeTake st novec lim = .ok (stF, st.free.back!) := by
      simp only [pikeTake]
      rw [if_pos hpos, hstF]
    rw [hred]
    show Runs p "pike_take" (takeArgs st novec lim)
      (takeArgs stF novec lim, some (markVal st.free.back!))
    rw [houts] at hruns
    exact hruns
  · -- The free list is empty: a fresh handle, its growth charged first.
    have hc1 : evalExpr p env0
        (.cmp .gt (.len (.var "free")) (.litInt .u32 0))
        = .ok (.bool false) := by
      rw [evalExpr_cmp (evalExpr_len (evalExpr_var h0free))
        (evalExpr_lit (t := .u32) (v := 0))]
      show Res.ok (Value.bool
        (decide (((st.free.toList.map markVal).length : Int) > 0))) = _
      rw [decide_eq_false (by simp only [List.length_map,
        Array.length_toList]; omega)]
    have hif1 : ∀ f, evalStmt f p
        (.ifS (.cmp .gt (.len (.var "free")) (.litInt .u32 0))
          [.letS "tmp1" (.int .u32) (some (.litInt .u32 0)),
           .pop (.var "free") (.var "tmp1"),
           .assign (.index (.var "rc") (.var "tmp1")) (.litInt .u32 1),
           .returnS (some (.var "tmp1"))] []) env0
        = some (.ok (env0, .normal)) := fun f => by
      rw [evalStmt_if_false hc1, evalStmts_nil]
    obtain ⟨env1, henv1⟩ : ∃ e : Env,
        env0.declare "tmp2" (.int .u32) (.int (st.rc.size : Nat)) = e :=
      ⟨_, rfl⟩
    have h1 : ∀ f, evalStmt f p
        (.letS "tmp2" (.int .u32) (some (.len (.var "rc")))) env0
        = some (.ok (env1, .normal)) := fun f => by
      rw [evalStmt_let (show evalExpr p env0 (.len (.var "rc"))
          = .ok (.int (st.rc.size : Nat)) by
        rw [evalExpr_len (evalExpr_var h0rc)]; simp), henv1]
    have h1tmp2 : env1.get "tmp2"
        = some ⟨.int .u32, .int (st.rc.size : Nat)⟩ := by store [← henv1]
    have hmb : Pcrevera.Ref.maxBlocks = 262796 := by decide
    by_cases hbig : st.rc.size ≥ 262796
    · -- The block table is at its declared maximum: both sides refuse.
      have hc2 : evalExpr p env1
          (.cmp .ge (.var "tmp2") (.litInt .u32 262796))
          = .ok (.bool true) := by
        rw [evalExpr_cmp (evalExpr_var h1tmp2)
          (evalExpr_lit (t := .u32) (v := 262796))]
        show Res.ok (Value.bool
          (decide ((st.rc.size : Int) ≥ 262796))) = _
        rw [decide_eq_true (by omega)]
      have hbody : ∀ f, evalStmts f p pikeTakeFunc.body env0
          = some (.ok (env1, .ret (some (.int 4294967295)))) := by
        intro f
        rw [pikeTakeFunc_body]
        unfold pikeTakeBody
        rw [evalStmts_cons (hif1 f), evalStmts_cons (h1 f)]
        refine evalStmts_cons_abrupt (by simp) ?_
        rw [evalStmt_if_true hc2,
          evalStmts_cons_abrupt (by simp)
            (evalStmt_return_some
              (evalExpr_lit (t := .u32) (v := 4294967295)))]
      have hruns := runs_of_body hf (inner := env1)
        (flow := .ret (some (.int 4294967295)))
        ⟨1, by rw [henv0]; exact hbody 1⟩
      have houts : outsOf pikeTakeFunc.params env1
          = takeArgs st novec lim := by
        store [outsOf, pikeTakeFunc_params, takeArgs, List.map_cons,
          List.map_nil, ← henv1, h0pool, h0rc, h0free, h0nov, h0mem, h0peak,
          h0cost, h0meml, h0costl]
      have hred : pikeTake st novec lim = .error st := by
        simp only [pikeTake]
        rw [if_neg hpos, if_pos (by omega : st.rc.size ≥ Pcrevera.Ref.maxBlocks)]
      rw [hred]
      show Runs p "pike_take" (takeArgs st novec lim)
        (takeArgs st novec lim, some (.int 4294967295))
      rw [houts] at hruns
      exact hruns
    · -- Room for one more: the growth is charged, then the fill runs.
      have hc2 : evalExpr p env1
          (.cmp .ge (.var "tmp2") (.litInt .u32 262796))
          = .ok (.bool false) := by
        rw [evalExpr_cmp (evalExpr_var h1tmp2)
          (evalExpr_lit (t := .u32) (v := 262796))]
        show Res.ok (Value.bool
          (decide ((st.rc.size : Int) ≥ 262796))) = _
        rw [decide_eq_false (by omega)]
      have hif2 : ∀ f, evalStmt f p
          (.ifS (.cmp .ge (.var "tmp2") (.litInt .u32 262796))
            [.returnS (some (.litInt .u32 4294967295))] []) env1
          = some (.ok (env1, .normal)) := fun f => by
        rw [evalStmt_if_false hc2, evalStmts_nil]
      obtain ⟨env2, henv2⟩ : ∃ e : Env,
          env1.declare "tmp3" .bool (.bool false) = e := ⟨_, rfl⟩
      have h2 : ∀ f, evalStmt f p
          (.letS "tmp3" .bool (some (.litBool false))) env1
          = some (.ok (env2, .normal)) := fun f => by
        rw [evalStmt_let evalExpr_litBool, henv2]
      have h2rc : env2.get "rc" = some ⟨.vec (.int .u32) 262796,
          .seq 262796 (st.rc.toList.map markVal) st.rcCap⟩ := by
        store [← henv2, ← henv1, h0rc]
      have h2mem : env2.get "mem"
          = some ⟨.int .counter, markVal st.m.mem⟩ := by
        store [← henv2, ← henv1, h0mem]
      have h2peak : env2.get "peak"
          = some ⟨.int .counter, markVal st.m.peak⟩ := by
        store [← henv2, ← henv1, h0peak]
      have h2cost : env2.get "cost"
          = some ⟨.int .counter, markVal st.m.cost⟩ := by
        store [← henv2, ← henv1, h0cost]
      have h2tmp3 : env2.get "tmp3" = some ⟨.bool, .bool false⟩ := by
        store [← henv2]
      have h2meml : env2.get "memlimit"
          = some ⟨.int .counter, markVal lim.mem⟩ := by
        store [← henv2, ← henv1, h0meml]
      have h2costl : env2.get "costlimit"
          = some ⟨.int .counter, markVal lim.cost⟩ := by
        store [← henv2, ← henv1, h0costl]
      have hargs : evalArgs p env2 cg.params
          [.inArg (.cap (.var "rc")), .inArg (.len (.var "rc")),
           .inArg (.litInt .u32 4), .inArg (.litInt .u32 262796),
           .inoutArg (.var "mem"), .inoutArg (.var "peak"),
           .inoutArg (.var "cost"),
           .inArg (.var "memlimit"), .inArg (.var "costlimit")]
          = .ok (cgArgs st.rcCap st.rc.size 4 262796 st.m lim) := by
        rw [hcgp]
        simp only [chargeGrowParams, evalArgs,
          evalExpr_cap (evalExpr_var h2rc), evalExpr_len (evalExpr_var h2rc),
          evalExpr_lit, readPlace_var h2mem, readPlace_var h2peak,
          readPlace_var h2cost, evalExpr_var h2meml, evalExpr_var h2costl,
          Res.ok_bind]
        simp [cgArgs, markVal]
      have hrun := hcg st.rcCap st.rc.size Pcrevera.Ref.regSize
        Pcrevera.Ref.maxBlocks st.m lim hrcap (by decide) (by decide)
        (by decide) hmem hcost
      match hgrow : chargeGrow st.rcCap st.rc.size Pcrevera.Ref.regSize
          Pcrevera.Ref.maxBlocks st.m lim with
      | none =>
          -- The charge refused; nothing moved, and both sides say no.
          rw [hgrow] at hrun
          obtain ⟨env3, henv3⟩ : ∃ e : Env,
              ((((env2.set "mem" (markVal st.m.mem)).set "peak"
                (markVal st.m.peak)).set "cost" (markVal st.m.cost)).set "tmp3"
                (.bool false)) = e := ⟨_, rfl⟩
          obtain ⟨nc, hcall⟩ := evalStmt_call_outs (dest := some (.var "tmp3"))
            hcgf hargs hrun (hcgp ▸ cgOuts_present)
          store [hcgp, chargeGrowParams, writeOuts, cgOuts, h2mem, h2peak,
            h2cost, h2tmp3, henv3] at hcall
          have h3tmp3 : env3.get "tmp3" = some ⟨.bool, .bool false⟩ := by
            store [← henv3, h2tmp3]
          have hbody : evalStmts nc p pikeTakeFunc.body env0
              = some (.ok (env3, .ret (some (.int 4294967295)))) := by
            rw [pikeTakeFunc_body]
            unfold pikeTakeBody
            rw [evalStmts_cons (hif1 nc), evalStmts_cons (h1 nc),
              evalStmts_cons (hif2 nc), evalStmts_cons (h2 nc),
              evalStmts_cons hcall]
            refine evalStmts_cons_abrupt (by simp) ?_
            rw [evalStmt_if_true (evalExpr_not (b := false)
                (evalExpr_var h3tmp3)),
              evalStmts_cons_abrupt (by simp)
                (evalStmt_return_some
                  (evalExpr_lit (t := .u32) (v := 4294967295)))]
          have hruns := runs_of_body hf (inner := env3)
            (flow := .ret (some (.int 4294967295)))
            ⟨nc, by rw [henv0]; exact hbody⟩
          have houts : outsOf pikeTakeFunc.params env3
              = takeArgs st novec lim := by
            store [outsOf, pikeTakeFunc_params, takeArgs, List.map_cons,
              List.map_nil, ← henv3, ← henv2, ← henv1, h0pool, h0rc, h0free,
              h0nov, h0mem, h0peak, h0cost, h0meml, h0costl]
          have hred : pikeTake st novec lim = .error st := by
            simp only [pikeTake]
            rw [if_neg hpos, if_neg (by omega :
              ¬st.rc.size ≥ Pcrevera.Ref.maxBlocks), hgrow]
          rw [hred]
          show Runs p "pike_take" (takeArgs st novec lim)
            (takeArgs st novec lim, some (.int 4294967295))
          rw [houts] at hruns
          exact hruns
      | some pr =>
          obtain ⟨m1, rcCap1⟩ := pr
          rw [hgrow] at hrun
          obtain ⟨env3, henv3⟩ : ∃ e : Env,
              ((((env2.set "mem" (markVal m1.mem)).set "peak"
                (markVal m1.peak)).set "cost" (markVal m1.cost)).set "tmp3"
                (.bool true)) = e := ⟨_, rfl⟩
          obtain ⟨nc, hcall⟩ := evalStmt_call_outs (dest := some (.var "tmp3"))
            hcgf hargs hrun (hcgp ▸ cgOuts_present)
          store [hcgp, chargeGrowParams, writeOuts, cgOuts, h2mem, h2peak,
            h2cost, h2tmp3, henv3] at hcall
          have h3tmp3 : env3.get "tmp3" = some ⟨.bool, .bool true⟩ := by
            store [← henv3, h2tmp3]
          have hif3 : ∀ f, evalStmt f p
              (.ifS (.un .not (.var "tmp3"))
                [.returnS (some (.litInt .u32 4294967295))] []) env3
              = some (.ok (env3, .normal)) := fun f => by
            rw [evalStmt_if_false (evalExpr_not (b := true)
              (evalExpr_var h3tmp3)), evalStmts_nil]
          have h3rc : env3.get "rc" = some ⟨.vec (.int .u32) 262796,
              .seq 262796 (st.rc.toList.map markVal) st.rcCap⟩ := by
            store [← henv3, h2rc]
          -- The push onto `rc` stays under the branch's own check, and the
          -- two growth rules agree on the capacity it leaves.
          have hml : (st.rc.toList.map markVal).length = st.rc.size := by
            simp
          have hgrownRc := chargeGrow_cap hrc (by rw [hmb]; exact hrcap) hgrow
          rw [hmb] at hgrownRc
          obtain ⟨env4, henv4⟩ : ∃ e : Env, env3.set "rc"
              (.seq 262796 ((st.rc.push 1).toList.map markVal) rcCap1) = e :=
            ⟨_, rfl⟩
          have hpush : ∀ f, evalStmt f p
              (.push (.var "rc") (.litInt .u32 1)) env3
              = some (.ok (env4, .normal)) := by
            intro f
            rw [evalStmt_push_var h3rc (evalExpr_lit (t := .u32) (v := 1))
                (by rw [hml]; omega),
              show (if (st.rc.toList.map markVal).length = st.rcCap
                  then grown 262796 st.rcCap else st.rcCap) = rcCap1 by
                rw [hml]; exact hgrownRc.2.2.2,
              show st.rc.toList.map markVal ++ [Value.int 1]
                  = (st.rc.push 1).toList.map markVal by simp [markVal],
              henv4]
          obtain ⟨env5, henv5⟩ : ∃ e : Env,
              env4.declare "tmp4" (.int .u32) (.int 0) = e := ⟨_, rfl⟩
          have h5 : ∀ f, evalStmt f p
              (.letS "tmp4" (.int .u32) (some (.litInt .u32 0))) env4
              = some (.ok (env5, .normal)) := fun f => by
            rw [evalStmt_let (evalExpr_lit (t := .u32) (v := 0)), henv5]
          obtain ⟨st1, hst1⟩ : ∃ s : PikeSt, ({ st with m := m1, rcCap := rcCap1, rc := st.rc.push 1 } : PikeSt) = s := ⟨_, rfl⟩
          have hst5 : FillSt env5 st1
            (.seq 262796 ((st.rc.push 1).toList.map markVal) rcCap1)
            (.seq 262796 (st.free.toList.map markVal) st.freeCap)
            (.int (st.rc.size : Nat)) novec 0 lim := by
            rw [← hst1]
            refine ⟨?_, ⟨true, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              store [← henv5, ← henv4, ← henv3, ← henv2, ← henv1, markVal,
                h3tmp3, h0nov, h0pool, h0rc, h0free, h1tmp2, h0mem, h0peak,
                h0cost, h0meml, h0costl] <;> rfl
          have hloop := fillLoop hcg hcgf hcgp hmem hcost hnovec novec 0 st1
            env5 _ _ _ (by omega)
            (by rw [← hst1]; exact hpool) (by rw [← hst1]; exact hpcap) hst5
          have hred0 : pikeTake st novec lim
              = match pikeTake.fill lim novec st1 with
                | .error stE => .error stE
                | .ok stO => .ok (stO, st.rc.size) := by
            simp only [pikeTake]
            rw [if_neg hpos, if_neg (by omega :
              ¬st.rc.size ≥ Pcrevera.Ref.maxBlocks), hgrow]
            simp only []
            rw [hst1]
            rfl
          match hfill : pikeTake.fill lim novec st1 with
          | .ok st2 =>
              rw [hfill] at hloop
              obtain ⟨n, env', hwhile, i', hstF⟩ := hloop
              have hframe := fill_frame novec st1 st2 (Or.inl hfill)
              have hbody : evalStmts (max nc n) p pikeTakeFunc.body env0
                  = some (.ok (env', .ret (some (.int (st.rc.size : Nat))))) := by
                rw [pikeTakeFunc_body]
                unfold pikeTakeBody
                rw [evalStmts_cons (hif1 _), evalStmts_cons (h1 _),
                  evalStmts_cons (hif2 _), evalStmts_cons (h2 _),
                  evalStmts_cons (evalStmt_mono hcall (Nat.le_max_left _ _)),
                  evalStmts_cons (hif3 _), evalStmts_cons (hpush _),
                  evalStmts_cons (h5 _),
                  evalStmts_cons (by
                    rw [evalStmt_while]
                    exact evalWhile_mono hwhile (Nat.le_max_right _ _)),
                  evalStmts_cons_abrupt (by simp)
                    (evalStmt_return_some (evalExpr_var hstF.tmp2))]
              have hruns := runs_of_body hf (inner := env')
                (flow := .ret (some (.int (st.rc.size : Nat))))
                ⟨max nc n, by rw [henv0]; exact hbody⟩
              have houts : outsOf pikeTakeFunc.params env'
                  = takeArgs st2 novec lim := by
                store [outsOf, pikeTakeFunc_params, takeArgs, List.map_cons,
                  List.map_nil, hstF.pool, hstF.rc, hstF.free, hstF.nov,
                  hstF.mem, hstF.peak, hstF.cost, hstF.meml, hstF.costl,
                  hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2, ← hst1]
              rw [hred0, hfill]
              show Runs p "pike_take" (takeArgs st novec lim)
                (takeArgs st2 novec lim, some (markVal st.rc.size))
              rw [houts] at hruns
              exact hruns
          | .error st2 =>
              rw [hfill] at hloop
              obtain ⟨n, env', hwhile, i', hstF⟩ := hloop
              have hframe := fill_frame novec st1 st2 (Or.inr hfill)
              have hbody : evalStmts (max nc n) p pikeTakeFunc.body env0
                  = some (.ok (env', .ret (some (.int 4294967295)))) := by
                rw [pikeTakeFunc_body]
                unfold pikeTakeBody
                rw [evalStmts_cons (hif1 _), evalStmts_cons (h1 _),
                  evalStmts_cons (hif2 _), evalStmts_cons (h2 _),
                  evalStmts_cons (evalStmt_mono hcall (Nat.le_max_left _ _)),
                  evalStmts_cons (hif3 _), evalStmts_cons (hpush _),
                  evalStmts_cons (h5 _),
                  evalStmts_cons_abrupt
                    (f := .ret (some (.int 4294967295))) (by simp) (by
                      rw [evalStmt_while]
                      exact evalWhile_mono hwhile (Nat.le_max_right _ _))]
              have hruns := runs_of_body hf (inner := env')
                (flow := .ret (some (.int 4294967295)))
                ⟨max nc n, by rw [henv0]; exact hbody⟩
              have houts : outsOf pikeTakeFunc.params env'
                  = takeArgs st2 novec lim := by
                store [outsOf, pikeTakeFunc_params, takeArgs, List.map_cons,
                  List.map_nil, hstF.pool, hstF.rc, hstF.free, hstF.nov,
                  hstF.mem, hstF.peak, hstF.cost, hstF.meml, hstF.costl,
                  hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2, ← hst1]
              rw [hred0, hfill]
              show Runs p "pike_take" (takeArgs st novec lim)
                (takeArgs st2 novec lim, some (.int 4294967295))
              rw [houts] at hruns
              exact hruns

end Pcrevera.Tir
