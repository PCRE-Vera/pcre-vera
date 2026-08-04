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

## `Array.ext` wants `apply`, not `refine … _ _ …`

`Array.ext` at this toolchain takes the two arrays implicitly and leaves a
size goal and an elementwise goal, so `refine Array.ext _ _ h ?_` reports
"function expected". `apply Array.ext` followed by the two goals is the
shape that works, and the elementwise goal arrives as `i`, `h₁ : i < a.size`,
`h₂ : i < b.size`.

## `omega` atomizes definitionally equal terms separately

A hypothesis about `st.pool.size` and a goal about `{ st with m := … }.pool.size`
give omega two unrelated atoms even though the two are the same by `rfl`.
Restate the hypothesis at the wanted type with a `have` — the coercion is
free — before reaching for omega.

## `first | (tac; by-term) | …` does not back out of a failed `by`

An alternative like `exact absurd h (by simp)` is accepted by `first` as
soon as the `exact` elaborates; the `by simp` hole is postponed and, when it
fails, is reported as an unsolved goal rather than sending `first` to the
next alternative. Any alternative meant to be tried and rejected has to fail
*synchronously* — put the discriminating work in the tactic itself, or order
the alternatives so the catch-all comes last.

## Structure instance fields are parsed at the first field's column

`{ st with a := x,` followed by a continuation line indented to the column of
`st` rather than of `a` stops the parser at the comma with "unexpected
identifier; expected '}'". Breaking the line straight after `with` and
putting every field one indent in always works.

## `conv_lhs` does not exist without Mathlib

`conv_lhs => rw [h]` is reported as "unknown tactic" on a plain Lean 4.32
toolchain with only Batteries: the `conv_lhs`/`conv_rhs` shorthands are
Mathlib macros. `conv => lhs; rw [h]` is the core spelling and works.

## A docstring goes below `set_option … in`, not above it

`/-- … -/` followed by `set_option maxHeartbeats 1000000 in` followed by
`theorem` does not parse; the error names the `set_option` token and looks
like a problem with the previous declaration. The order Lean wants is
`set_option … in`, then the docstring, then the declaration.

## `split at h` does not always take the outermost `if`

On a hypothesis whose type nests several `if`s, `split at h` may pick an
inner one, so a chain of `split at h` / `rename_i` produces hypotheses about
conditions other than the ones the source reads left to right. Unfolding
with `by_cases` on each condition and `rw [if_pos h] / rw [if_neg h]` is
deterministic and is worth the extra lines whenever the names matter.

## `getElem!_pos` wants its array and index explicit

`rw [getElem!_pos _ _ h]` fails to elaborate the `GetElem?` instance and
reports a synthesis failure at `Nat`. Writing `rw [getElem!_pos a i h]` with
both arguments given works.

## `rw` with a definition's equation unfolds one instantiation, not all

`rw [buildLive]` on a goal mentioning `buildLive true st ext₁` and
`buildLive true st ext₂` instantiates the equation at whichever it meets
first and leaves the other folded. `simp only [buildLive]` unfolds every
instance, which is almost always what is wanted when both sides of a
`Perm` goal are built from the same definition.

## `simpa only [f, if_pos rfl]` can leave `if True then … else …`

Unfolding a definition whose body is an `ite` and asking simp to take the
positive branch in the same call sometimes normalises the *condition* to
`True` without reducing the `ite`. Proving the reduced equation on its own
first — `have : f a = [] := by rw [f, if_pos rfl]` — and rewriting with it
is stable.

## `rw` closing a goal by `rfl` leaves the next tactic with nothing

A `rw` whose result is a syntactic identity closes the goal itself, so a
following `simp` in the same alternative reports "no goals to be solved"
and, inside a `first` chain, takes the whole alternative down. `subst`
before the `simp` — or a `first | rfl | simp` — keeps the script honest
across branches that differ in whether the rewrite lands on `rfl`.

## `by_contra` does not exist without Mathlib

Like `conv_lhs`, `by_contra` is a Mathlib tactic and is reported as "unknown
tactic" on a plain Lean 4.32 toolchain. Case on the decidable proposition
with `rcases Nat.lt_or_ge …` / `by_cases`, or derive the fact from a
hypothesis already in scope.

## `cases h : e` substitutes in the goal but not in hypotheses

After `cases hk : (re.regions[i]!).kind`, the goal already mentions the
constructor, so `rw [hk] at ⊢` fails with "did not find an occurrence of the
pattern". Only `rw [hk] at h` is needed, and it is needed for every
hypothesis that still mentions the scrutinee.

## `omega` sees a structure projection of a literal as an atom

After `rw [hinfo]` a goal reads `lo + 1 ≤ { lo := …, head := lo + 1, … }.head`,
which is true by `rfl`, and omega still fails: it does not reduce the
projection, so it takes the whole `{ … }.head` for an opaque natural and
reports a counterexample. `show lo + 1 ≤ lo + 1` first — the projection of a
literal is defeq to the field — or close the goal with `Nat.le_refl _` and
skip omega. The same applies to `Inst.arg` and `Inst.op` after rewriting a
cell to `⟨.repZero, r, 0⟩`.

## `decide` refuses a proposition that mentions a free variable

`absurd hq (by decide)` on `¬ ((⟨.cls, idx, 0⟩ : Inst).op = Op.repZero)` fails
with "Expected type must not contain free variables", even though `.op`
reduces to `Op.cls` whatever `idx` is: `decide` looks at the stated type
before any reduction. `fun hq => by simp at hq` does the job — simp reduces
the projection, turns the equation into `False`, and closes whatever goal was
open.

## `rw` does not match through a projection of a literal

With `hinfo : reps[r0]! = ⟨…⟩` and a goal about
`reps[(⟨.repNext, r0, 0⟩ : Inst).arg]!`, `rw [hinfo]` has nothing to match:
keyed matching wants `reps[r0]!` syntactically and the index is still a
projection. `simp [hinfo]` reduces the projection first and then rewrites,
and it also normalises the `j + 1 - 1` a repetition row's `after - 1` leaves
behind.

## `open private … from` takes a module name, not a namespace

`open private rootSt from Pcrevera.Refine` does not resolve; the argument is
the module the declaration lives in, so it is
`open private rootSt from Pcrevera.Proofs.Refine`. It has to sit at the top
level, before the `namespace` that will use the name.

## `Array.foldl_toList` goes from the list to the array, not the other way

`theorem Array.foldl_toList : as.toList.foldl f init = as.foldl f init`. The
name reads as if it rewrote an array fold into a list fold, and it is stated
the other way round, so a proof that wants to reach a list fold rewrites with
`← Array.foldl_toList` — or, as here, states the list side and finishes with
the array side on the right.

## `List.take_add_one` splits off an `Option`, not an element

`l.take (n + 1) = l.take n ++ l[n]?.toList`. Reaching for a `l.take n ++
[l[n]]` shape and proving `n < l.length` first is the reflex; the library
does not need the bound because it appends `l[n]?.toList`, which is empty
past the end. With the bound in hand, `List.getElem?_eq_getElem` turns the
option into `some l[n]` and `Option.toList_some` finishes the job.

## `rw [Nat.add_zero]` rewrites one instance, `simp only` rewrites them all

`rw` instantiates the lemma's metavariables from the first match it finds and
then rewrites every occurrence *of that instance*. A goal holding both
`1 + 0` and `x + 0` therefore needs two `rw`s, in the right order, and the
second fails outright if the first already consumed its match. `simp only
[Nat.add_zero]` does the obvious thing and is what to reach for when the
instances differ.

## A constant has to be unfolded everywhere omega will look

`simp only [regSize] at hcost ⊢` leaves every other hypothesis — including
the one `split` has just introduced anonymously — with `regSize` opaque, and
omega then treats `k * regSize` and `k * 4` as unrelated atoms. Name the
branch hypothesis with `rename_i` and unfold the constant there too, or use
`at *`.

## Anonymous constructors pin implicit arguments before the later ones are seen

`Trans.trans ⟨rfl, rfl⟩ h` elaborates the anonymous constructor first, which
forces the middle term to whatever makes the `rfl`s typecheck, and `h` is
then rejected. Introduce the middle term with a `have` carrying its full
type, then compose.
