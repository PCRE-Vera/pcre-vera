import Pcrevera.Tir.Stable

/-!
# Four small programs, run

Gate 1's own test. The interpreter is total by construction and stable in its
budget, but neither says it computes the right thing — only that it computes
something, always the same. So here are four programs whose answers are known
before the interpreter is asked, one for each thing that could be quietly
wrong: a loop that runs to a bound, a loop that leaves early, the counter
saturation of section 6.7 which is a pre-check rather than a clamp, and an
index past the end, which is an outcome and not a crash.

`#guard` runs them at elaboration time and fails the build on a wrong answer,
which is what a check is for. It is not a proof and does not pretend to be:
the definitions are well-founded rather than structural, so the kernel cannot
reduce them, and a `decide` here would have to reach for `native_decide` and
an axiom this project does not take.
-/

namespace Pcrevera.Tir

private def u32 : Ty := .int .u32
private def counter : Ty := .int .counter

/-- `sum(n)` adds 1 through n. The variant is the remaining count, which the
Python interpreter checks at run time and the fuel here does not read. -/
def sumProgram : Program where
  enums := []
  structs := []
  consts := []
  funcs := [
    { name := "sum"
      params := [⟨"n", u32, false⟩]
      ret := some u32
      body := [
        .letS "acc" u32 (some (.litInt .u32 0)),
        .letS "i" u32 (some (.litInt .u32 0)),
        .whileS (.cmp .lt (.var "i") (.var "n"))
          (.bin .sub (.cast counter (.var "n")) (.cast counter (.var "i")))
          [ .assign (.var "i") (.bin .add (.var "i") (.litInt .u32 1)),
            .assign (.var "acc") (.bin .add (.var "acc") (.var "i")) ],
        .returnS (some (.var "acc")) ] }]

#guard callFunc 200 sumProgram "sum" [.int 10]
    == some (.ok ([.int 10], some (.int 55)))

#guard callFunc 200 sumProgram "sum" [.int 0]
    == some (.ok ([.int 0], some (.int 0)))

-- A budget too small answers `none` rather than a wrong number.
#guard callFunc 3 sumProgram "sum" [.int 10] == none

/-- `firstAbove(n)` stops at the first multiple of three past `n`, by leaving
the loop early. A `break` has to end the loop and nothing else. -/
def breakProgram : Program where
  enums := []
  structs := []
  consts := []
  funcs := [
    { name := "firstAbove"
      params := [⟨"n", u32, false⟩]
      ret := some u32
      body := [
        .letS "i" u32 (some (.var "n")),
        .whileS (.litBool true) (.litInt .counter 0)
          [ .assign (.var "i") (.bin .add (.var "i") (.litInt .u32 1)),
            .ifS (.cmp .eq (.divrem .rem (.var "i") (.litInt .u32 3)
                (.litInt .u32 1)) (.litInt .u32 0))
              [.breakS] [] ],
        .returnS (some (.var "i")) ] }]

#guard callFunc 200 breakProgram "firstAbove" [.int 7]
    == some (.ok ([.int 7], some (.int 9)))

#guard callFunc 200 breakProgram "firstAbove" [.int 9]
    == some (.ok ([.int 9], some (.int 12)))

/-- The counter saturation, which is the one arithmetic rule stated as a
pre-check: `cap - 1` plus two is the cap, not a wrapped small number, and the
cap minus more than it holds is zero rather than negative. -/
def saturateProgram : Program where
  enums := []
  structs := []
  consts := []
  funcs := [
    { name := "climb"
      params := [⟨"start", counter, false⟩, ⟨"by", counter, false⟩]
      ret := some counter
      body := [.returnS (some (.bin .add (.var "start") (.var "by")))] },
    { name := "fall"
      params := [⟨"start", counter, false⟩, ⟨"by", counter, false⟩]
      ret := some counter
      body := [.returnS (some (.bin .sub (.var "start") (.var "by")))] }]

#guard callFunc 10 saturateProgram "climb" [.int (2 ^ 53 - 2), .int 2]
    == some (.ok ([.int (2 ^ 53 - 2), .int 2], some (.int (2 ^ 53 - 1))))

#guard callFunc 10 saturateProgram "climb" [.int 3, .int 4]
    == some (.ok ([.int 3, .int 4], some (.int 7)))

#guard callFunc 10 saturateProgram "fall" [.int 3, .int 40]
    == some (.ok ([.int 3, .int 40], some (.int 0)))

/-- A trap is an outcome, not a crash: an index past the end answers T-01. -/
def trapProgram : Program where
  enums := []
  structs := []
  consts := []
  funcs := [
    { name := "reach"
      params := [⟨"v", .vec u32 8, true⟩, ⟨"at", u32, false⟩]
      ret := some u32
      body := [.returnS (some (.index (.var "v") (.var "at")))] }]

#guard callFunc 10 trapProgram "reach" [.seq 8 [.int 5, .int 6] 2, .int 1]
    == some (.ok ([.seq 8 [.int 5, .int 6] 2, .int 1], some (.int 6)))

#guard callFunc 10 trapProgram "reach" [.seq 8 [.int 5, .int 6] 2, .int 4]
    == some (.trap "T-01")

end Pcrevera.Tir
