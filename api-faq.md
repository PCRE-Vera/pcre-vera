# APIs that did not behave the way we first assumed

Kept so the same surprise costs an hour once, not every time.

## `node --test <directory>` no longer scans the directory

Written as `node --test test/`, the way the Node documentation showed for
years. On Node 26 that fails with `Cannot find module '.../gen/js/test'`: a
positional argument is now resolved as a module path, not as a directory to
search.

The fix is to pass no path at all. `node --test` runs its own discovery from
the current directory, picking up `**/*.test.mjs` and friends and skipping
`node_modules`, which is what the directory argument was standing in for
anyway. The test script in `gen/js/package.json`, the `js` target in the
Makefile, and the CI job all use the bare form.

## `pcre2_config(PCRE2_CONFIG_VERSION, buf)` returns a length that includes the NUL

The obvious reading is that the return value is the string length, as with
`strlen`. It is one more than that: pcre2 counts the terminating NUL. Passing
the returned length straight to a hex encoder puts a stray `00` at the end of
every version string. The shim subtracts one, for `PCRE2_CONFIG_VERSION` and
`PCRE2_CONFIG_UNICODE_VERSION` alike.

## pcre2 compile error codes are offset by 100

The error numbering in `pcre2_error.c` starts at `ERR1`, so it is tempting to
expect `pcre2_compile` to report 14 for "missing closing parenthesis". It
reports 114: the public codes returned through `errorcodeptr` add
`COMPILE_ERROR_BASE`, which is 100. The seed corpus and, later, our own engine
speak the public numbering.

## `tarfile.extractall` needs `filter="data"` to be safe

Not a surprise so much as a version trap. The default filter changed to `data`
in Python 3.14; on 3.12 and 3.13, which this project still supports, the
default is the old permissive behavior that honours absolute paths, `..`
components, and device entries. Saying `filter="data"` outright means the same
policy on every supported version, which the oracle build does even though the
tarball it unpacks is hash-pinned.

## `set` is a Mathlib tactic, not core and not batteries

Written `set stM := ... with hstM` out of habit; on a batteries-only
project that is an unknown tactic. There is no drop-in replacement —
`generalize ... at *` fights dependent occurrences — so the proofs in
`RefineProto.lean` just spell the terms out. Same story for `conv_lhs`:
core spells it `conv => lhs; ...`.

## Structure-instance fields end at the line break

`{ st with code := (x.modify i fun i => ...) }` split over two lines parses
the continuation as a new field and dies with "unexpected token, expected
'}'". Wrapping the whole field value in one extra pair of parentheses lets
it span lines.

## `(a.push x).size` is not defeq to `a.size + 1` on an abstract array

`Array.size_push` is a theorem, not a reduction. A characterization lemma
meant to be closed by `rfl` must spell `(a.push x).size`, not `a.size + 1`
— the mismatch surfaced as an opaque `rfl` failure on a `compileAlt`
unfolding.

## Private defs from another file: nameable via batteries, defeq always

`emit`/`patch`/`openRegion`/`closeRegion` are private to `Ref/Compile.lean`.
Two facts made the compiler proofs possible without touching that file:
`open private emit patch ... from Pcrevera.Ref.Compile` (batteries'
`Batteries.Tactic.OpenPrivate`) makes the names resolvable, and even
without it the kernel unfolds private plain defs, so `rfl` proves
equations whose statement avoids the private names.

## `omega` does not unfold plain defs

`1 ≤ counterMax` fails outright: `counterMax` is an ordinary def and
omega treats it as an opaque atom (it does handle `2 ^ 53` literals once
they are visible). Either `unfold counterMax` first, or hand omega a
`have hcm : counterMax = 2 ^ 53 - 1 := rfl` so the atom links up.

## `by_contra` needs a batteries import

On modules that only import project files (which bottom out in core),
`by_contra` is an unknown tactic. `rcases Nat.lt_or_ge ... with h | h`
plus `exfalso` covers the arithmetic uses without pulling anything in.

## `split at h` refuses ifs hidden under `let`/`have` redexes

An unfolded definition whose body began with `let` shows up as
non-dependent `have` binders, and `split at h` reports "could not split"
even though the if is right there. `simp only [] at h` beta-reduces the
redexes first and costs nothing else.

## Unifying a pair pattern against a pair-valued call goes badly

`(?seen, ?pending) =?= markSeen ...` makes the elaborator whnf the call,
which strands the goal on a stuck `Decidable.rec` and half-assigned
metavariables. Restate the helper over one variable of the product type
(`∀ mp : Array Bool × List Nat, ...` applied via `mp.1`/`mp.2` and
structure eta) and unification stays first-order.

## `split` cannot break an ite under a `let` from a WF equation

Rewriting `btFail` with its equation lemma leaves the body's `let`s in
place, and `split at h` refuses an `ite` whose condition mentions a
let-bound variable. The workaround that held up: state a private
equation whose right-hand side is the body with every let inlined by
hand (records composed, the pair destructuring gone through structure
eta) and prove it by `rw [f, dif_neg h]` — the trailing `rfl` check
closes it by zeta/iota, and the ite is then split-able.

## `cases h` on `some a = some x` substitutes and consumes `h`

In a `cases a <;> simp only [f] at h <;> try cases h` pipeline the
surviving hypotheses `h : some A = some x` are *eaten* by `cases h` —
it unifies `x := A` and removes `h`. A following `subst h` then fails
with "unknown identifier". Either drop the subst or don't `cases h`.

## `List.mem_of_mem_filter` is not there

Batteries at this toolchain has `List.mem_filter : a ∈ l.filter p ↔ a ∈ l
∧ p a = true` and nothing shorter, so a membership out of a filtered list
reads `(List.mem_filter.mp h).1`.

## Round-tripping a `Nat` through `UInt32`

`(n.toUInt32).toNat = n` under `n < 2 ^ 32` is
`simp [Nat.toUInt32, Nat.mod_eq_of_lt h]` — naming `UInt32.toNat_ofNat`
as well is flagged as an unused argument, the unfolding of `Nat.toUInt32`
already exposes the modulus. `(n + 1).toUInt32 = n.toUInt32 + 1` is
`simp [Nat.toUInt32]`, unconditionally. Injectivity below the wrap comes
from `congrArg UInt32.toNat` plus the same two rewrites.

## `rw` with the equations of a well-founded definition leaves side goals

For a `def` whose last arm is a catch-all, `rw [f]` on a specific
constructor produces the body *and* one goal per earlier pattern saying
the scrutinee is not that pattern. `simp [f]` closes them; `rw [f] <;>
simp` also works when the body still needs work.

## `Array.all_eq_true` hands you an index, not an element

`as.all p = true ↔ ∀ (i : Nat) (_ : i < as.size), p as[i] = true`. The
`List` twin quantifies over members, so the two are used differently:
`List.all_eq_true.mp h x hx` against `Array.all_eq_true.mp h i hi`. Passing
an anonymous constructor `⟨i, hi⟩` fails with "the expected type `Nat` has
more than one constructor".

## `by_contra` is a Mathlib tactic

The proofs here run on Batteries only. `rcases Nat.lt_or_ge a b with h | h`
does the job whenever the contradiction is about an order, and
`Classical.byContradiction` is there for the rest.

## `obtain ⟨…⟩ := f x ?_` puts the hole where you did not expect it

A synthetic hole inside the term of an `obtain` becomes a goal whose
position relative to the main goal is not the reading order of the script,
so a following `·` bullet pair reports "no goals to be solved". Proving the
side condition as a named `have` before the `obtain` is both shorter and
stable.

## A `∀` over `getElem!` indices needs the index type spelled

`∀ pc, (Array.replicate n false)[pc]! = false` leaves the index type a
metavariable and `GetElem?` resolution gets stuck on it. Write
`∀ pc : Nat, …`.

## `List.count_cons` compares the cons head against the counted element

`count a (b :: l) = count a l + if b == a then 1 else 0` — the head is on
the left of the `==`. A hypothesis in the shape `x ≠ h` is therefore the
wrong way round for `simp` to discharge the `if` when counting `x` in
`h :: rest`, and the simp argument is silently reported as unused. Two
one-line wrappers (`count a (a :: l) = count a l + 1`, and the `≠` case
with the flip built in) keep the direction out of every later proof.

## `simp [eq_comm]` loops

Reaching for `eq_comm` to line up an `if x = h` against an `if h = x`
rewrites forever and ends in "maximum recursion depth". Proving the
singleton count as its own lemma, by `by_cases` and `List.count_eq_zero`,
is both shorter and terminating.

## Batteries has no `List.Nodup.length_le_of_subset`

At this toolchain neither core nor Batteries has the "a duplicate-free list
is no longer than any list it is a subset of" lemma. Counting with
multiplicity instead — `∑_{k < n} l.count k ≤ l.length`, by induction on
`l` — needs only `List.count_cons` and gives the same bound without any
`Nodup` bookkeeping.

## `Array.getElem!` after `Array.set!` and `Array.push`

Core has `Array.getElem!_set!_self` and `Array.getElem!_set!_ne` (in
`Init.Data.Array.Lemmas`); the `ne` one wants the *set* index first, so the
side condition reads `i ≠ j` where `j` is the one being read. There is no
matching pair for `push`: `getElem!_pos` plus `Array.getElem_push_lt` is the
way, and `simp` does not find `getElem_push_lt` on its own.

## `Array.size_push` takes the pushed value explicitly

`Array.size_push : ∀ (v : α), (xs.push v).size = xs.size + 1`, so
`exact Array.size_push` against a fully applied goal is a type mismatch.
`by simp` closes it; `Array.size_set!` takes all three explicitly and is
fine as a rewrite.

## `exact ih hok` can pin an induction hypothesis' implicit arguments early

In `∀ {k st st'}, f k st = .ok st' → P st st'`, closing the step case with
`exact ih hok` elaborates the expected type first, which fixes `ih`'s
implicit state to the outer one before `hok` is even looked at. Destructing
the result — `obtain ⟨h1, h2⟩ := ih hok` and then rebuilding it — lets the
state come from `hok`, where it belongs.

## `rw [f.eq_def]` does not iota-reduce the match it exposes

Rewriting with a definition whose body is a `match` on a constructor
leaves the match standing; `rw`'s closing `rfl` sometimes lands and
sometimes does not, so a following `rw` at the exposed subterm fails to
find its pattern. The reliable shape is a one-line wrapper per arm —
`search_cat_eq`, `search_grp_eq` and friends, each proved by
`rw [Spec.search.eq_def]` and, where the arm has a guard of its own,
`simp only []` to zeta-reduce before `rw [if_pos …]`.

## `first | tac₁ | tac₂` does not catch errors inside a nested `by`

`exact absurd h (by simp)` in an alternative whose `by simp` fails logs an
error rather than failing the alternative, so `first` never moves on. Give
the alternative a plain term — a tiny lemma such as `absurd_error` above a
`first` chain — so that a branch it does not fit fails to elaborate
instead of failing to close.
