# The composition algebra

DESIGN.md section 5 says the resource analysis is split in two: an untrusted
analyzer searches for a bound certificate, and a small checker decides whether
to believe it. This document is the rule set they apply. It was written before
the analyzer existed on purpose — the analyzer may only claim things the
checker can verify, so the rules had to be settled first, or the analyzer would
have ended up introducing facts nothing can check.

Sections 1 through 8 are about `CfgBacktrack`, the backtracking VM of
`engine/vm.py`. Section 9 is `CfgPike`, the lockstep VM of `engine/pike.py`,
whose accounting is a whole-call closed form rather than a composition over
regions; `pike_check` is its transcription, and `cert_check` dispatches the
Pike configuration there. The memoized path waits for M9 and is refused by
name until then.

There are two implementations, and that is the point. `engine/analyzer.py`
walks the compiler's region tree in reverse emission order and computes a price
for each region out of the prices of its children; `engine/certificate.py`
takes a claimed price and reads it back against the bytecode. Neither calls the
other. What they do share is `engine/bounds.py` — the arithmetic of section 2
and the opcode table of section 3 — because DESIGN.md section 5 asks for one
cost model behind the analyzer, both matchers and the Lean accounting, and a
second copy of that is the easiest way to lose it. Sharing the composition
would be a different thing entirely: the checker's verdict would become a
restatement of the analyzer's own opinion.

Compiling a pattern runs the analyzer and then the checker, and stores the
certificate only if the checker accepts it. The corpus that holds both to this
document is `conformance/certificates.json`.

## 1. What is being bounded

Three numbers, the ones `match` reports back in its `Usage` and the ones
DESIGN.md section 2.4 exposes on the compiled pattern:

```text
+-------+----------------------------------------------------------------+
| cost  | cost units charged over the whole call                         |
| stack | the deepest the backtrack stack ever gets, in entries          |
| mem   | the peak scratch reservation, in IR bytes                      |
+-------+----------------------------------------------------------------+
```

A bound holds for every subject of length n, every start offset, and every
combination of match options.

Not because the options only ever remove work. They do not: `NOTEMPTY` refuses
a match the run had already found, and the search carries on from there, so
`a??` on one byte costs more units with it than without. `NOTBOL` and `NOTEOL`
can turn an early success into more searching the same way.

It holds because none of the rules below prices a particular run. They price
every path the program can take from every starting position, and every fork is
charged for both its arms whether or not a given run explores the second. An
option can turn a success into more searching, and the searching it turns into
was paid for in advance. That is the whole of the argument, and it is the shape
the Layer A obligation will take.

The same goes for the `ANCHORED` compile option. An anchored pattern really
does attempt one starting position rather than n + 1, and the rules here charge
it for n + 1 anyway. That is a factor the analysis leaves on the table, and it
is the first thing to sharpen if anchored patterns ever need a tighter number.

## 2. The arithmetic

A bound is one growth base and one coefficient per power of (n + 1):

    base^n * (c0 + c1*(n+1) + c2*(n+1)^2 + c3*(n+1)^3 + c4*(n+1)^4)

Base 1 is the polynomial case. A base above 1 is what structural ambiguity
inside an unbounded repetition produces, and it saturates within a few dozen
bytes of subject, which is the honest answer rather than a number nobody could
budget for.

Writing the powers in (n + 1) rather than in n is what makes this form usable.
Every basis function `base^n * (n+1)^d` is then at least 1 and nondecreasing in
both base and degree, which gives the three operations the composition rules
need:

- **Sum.** Coefficients add. If the two bases differ, the larger one is kept
  for the result. That over-approximates — `2^n + 1` becomes `2*2^n` — and it
  is sound precisely because every basis function is nonnegative and grows with
  its base.
- **Product.** Bases multiply, coefficients convolve. A product that would need
  a power above the fourth is a refusal, not a rounding.
- **Dominance.** `A` dominates `B` when its base is at least `B`'s and each of
  its coefficients is at least the matching one. That is sufficient and not
  necessary — `(n+1)^2` is above `(n+1)` and this rule says otherwise — which is
  the right way round for a checker. No inequality is ever established by
  evaluating both sides at a few subject lengths.

Every coefficient lives in a counter and every operation pre-checks the
saturation point of TIR-SPEC.md section 6.7. A requirement that saturates is
refused outright: a coefficient that stopped at the cap is one a certificate
would be found to satisfy while the truth sat above it.

A bound with no coefficients is zero at every length, and is normalized to base
1 so that a claim of zero is never refused for naming a smaller base than a
requirement that is also zero.

## 3. What one instruction costs

One cost unit per instruction visit, from the shared cost model of DESIGN.md
section 5. On top of that, three opcode groups touch the two growing arrays:

```text
+---------------------------------------+-------+-------+-------+
| opcode                                | visit | stack | trail |
+---------------------------------------+-------+-------+-------+
| Char CharCI Class Any AnyNoNL Bsr     |   1   |   0   |   0   |
| Circ CircM Doll DollE DollM           |   1   |   0   |   0   |
| Sod Eod Eodn WordB NotWordB           |   1   |   0   |   0   |
| Save                                  |   1   |   0   |   1   |
| Accept                                |   1   |   0   |   0   |
| Split                                 |   1   |   1   |   0   |
| Jump                                  |   1   |   0   |   0   |
| RepZero                               |   1   |   0   |   1   |
| RepLoop                               |   1   |   1   |   0   |
| RepEnter                              |   1   |   0   |   1   |
| RepNext                               |   1   |   0   |   1   |
+---------------------------------------+-------+-------+-------+
```

"stack" is backtrack entries pushed per visit and "trail" is undo entries
recorded per visit. Both are upper bounds rather than exact counts: `RepLoop`
forks only when the count is between the two declared bounds, and `write_reg`
records nothing while the backtrack stack is empty. Charging for them anyway is
what keeps the rule per-opcode instead of per-state.

The first five rows are the whole of what a region may hold loose. Everything
below them forks, jumps, or drives a repetition, and belongs to a region whose
kind says how to price it; meeting one outside such a region is the tree
failing to explain the program — the checker's `CrOpcode`.

Four charges do not appear in the table because they are not per-visit:

- **Growth.** `charge_grow` charges the new buffer plus the one being copied
  out of, one unit per IR byte, before allocating. Section 5 folds it into the
  whole-call total.
- **Setup and reset.** The register file and the ovector are zeroed once, and
  the registers are cleared again at every starting position. Also section 5.
- **Delivery.** A match copies the capture registers back into the caller's
  ovector, at the same four units each, and a call whose budget does not
  stretch to that has gone over it like any other. It happens at most once, so
  section 5 charges it once.
- **Replay.** A backtrack pop puts back every register the failed path wrote,
  at four units each — one per IR byte of the register, the same rate the reset
  charges. A register can only be put back if a `Save`, `RepZero`, `RepEnter`
  or `RepNext` recorded it, so the trail bound of section 4 prices the replay
  as well, and section 5 spends it there.

## 4. Regions

A region is a contiguous instruction range with a kind and a parent, and it is
the *compiler* that emits it. That is not an implementation detail: while it
lays out the bytecode it still has the AST in hand, and that is the one moment
anything knows that this stretch of instructions came from that quantifier.
Rediscovering it afterwards would mean reading structure back out of a flat,
cyclic control-flow graph.

So the table lives on the compiled pattern, and there is one of it. A
certificate holds a *price* per region, in the same order, and nothing else —
no second copy of the tree that could come to disagree with the first. One
price per region exactly: a claim about a region nobody emitted is refused, and
so is a region nobody priced.

None of which makes the tree trusted. Every rule below reads it back against
the bytecode, and a compiler that emitted a tree not describing its own output
would be refused the same way a hand-written one is.

Those rules are `cert_shape`, and they take no certificate. Whether a tree
describes a program is a question about the program, with the same answer
whether or not the composition rules can price the thing — so it is asked on
its own, by the checker before it looks at a claim and by compilation before it
asks the analyzer for anything. What is left in the pricing walk below is the
arithmetic. The split matters in one direction in particular: a compiler bug
that only showed up on patterns with no representable bound would otherwise
have been reported for none of them.

A price is what one *entry* into the region costs:

```text
+-------+---------------------------------------------------------------+
| work  | instruction visits inside the region                          |
| stack | backtrack entries pushed inside it                            |
| trail | undo entries recorded inside it                               |
| outs  | times control leaves it going forward                         |
+-------+---------------------------------------------------------------+
```

`outs` is the region's ambiguity, and it is the multiplier everything else
composes with: a construct that can succeed in three different ways hands the
construct after it three chances to run. Every quantity is linear in the flow
arriving at a region, which is why one number per region is enough and why the
rules below are all sums and products.

The checker prices each region from what its *children claim*, and then
requires the region's own claim to dominate what came out. Soundness is
therefore an induction one step deep: if every child's claim is an upper bound,
so is the parent's.

### 4.1 Straight-line regions: root, group, branch

Read the range left to right, carrying a flow that starts at one entry.

- At a child region: charge `flow * child.work`, `flow * child.stack` and
  `flow * child.trail`, then set `flow := flow * child.outs` and jump to the
  child's end.
- At an instruction the region holds itself: charge one visit and the trail
  entry of the table above, both times the flow. `Accept` additionally sets the
  flow to zero, since a match ends the attempt and nothing downstream is
  reached by way of it.

`outs` is the flow left at the end of the range.

A `RkBranch` is refused here unless its parent is an `RkAlt`. Section 4.2
refuses a child of an alternation that is not a branch, so between them the two
rules say that branches and alternations only ever come in pairs. And a region
whose kind is none of the five is refused outright, which is not the tautology
it looks like: an enum value is one of its variants in the IR and an ordinary
integer once printed, so the check is there for a caller of the generated code
that made one up.

A child met by *this* walk and covering no instruction is refused. It would
leave the walk where it was, and there is nothing such a region can say that
its parent does not already say. The compiler drops one rather than emitting
it: a construct that compiled to nothing has nothing inside it either, so its
region is still the last one in the table and can simply be taken back off.

The branches of an alternation are the exception, and they are an exception
because they are not met by this walk at all — section 4.2 reads them off the
branch list rather than off the code. An alternation of `a|` has a second arm
that compiles to nothing, and the record of it still has to be there, or the
shape check has no branch to line up against the split.

The root is a straight-line region whose range is the whole program. Its `outs`
is not used by anything: nothing follows the program.

### 4.2 Alternation

The compiler emits `split branch jump split branch jump ... branch`, with every
jump patched to the end of the alternation and every split's second arm
pointing at the next split. An `RkAlt` region's children are its `RkBranch`
regions, in order, and the shape is checked against the code: for every branch
but the last there must be a split whose fall-through arm is the branch's first
instruction and whose other arm is the instruction after the branch's closing
jump, and that jump must target the end of the region.

Each split is reached once per entry, and each branch is entered once, since
backtracking works its way along the chain of splits. So, for k branches:

    work  = (k-1) + sum(branch.work) + sum(branch.outs for all but the last)
    stack = (k-1) + sum(branch.stack)
    trail = sum(branch.trail)
    outs  = sum(branch.outs)

The jumps are the second sum in `work`: a branch's closing jump runs once per
way that branch found to succeed.

An alternation of one branch is refused. The compiler emits no split for it, so
a region claiming to be one is pricing instructions that are not there.

This is where the rules are at their most conservative. `outs` is the sum over
branches because nothing here knows that `a` and `b` cannot both match the same
byte, so `(a|b)*` comes out exponential. The bound may overestimate and never
underestimate (DESIGN.md section 5); a first-byte disjointness rule, which
would let the sum become a maximum, is the obvious next refinement and is the
kind of thing the analyzer would search for and this checker would verify.

### 4.3 Optional items

`a?` and `a??` compile to one split whose two arms are the body and what
follows, in whichever order the greediness asks for. With `b` the body's price:

    work  = 1 + b.work
    stack = 1 + b.stack
    trail = b.trail
    outs  = 1 + b.outs

The `1` in `outs` is skipping the body, which is a way out of the region too.

### 4.4 Counted repetitions

A counted repetition compiles to five parts:

    lo   : RepZero  r        zero the counter
    lo+1 : RepLoop  r        decide whether to go round again  (rep.head)
    lo+2 : RepEnter r        remember where this iteration began  (rep.body)
    ...  : the body
    hi-1 : RepNext  r        count, and jump back or fall out
    hi   :                   (rep.after)

The checker requires exactly that: the four opcodes in those positions, all
naming the same repetition `r`, and `reps[r].head`, `reps[r].body` and
`reps[r].after` equal to `lo+1`, `lo+2` and `hi`. Between the opcodes and the
three offsets there is nothing left for a region to choose, which answers the
question of whether a repeat region can identify the quantifier that drives it:
it can, from the code and the range alone, and no witness field is needed.

Let `b` be the body's price and `w = b.outs` its ambiguity. **`w` must be one
number** — a body whose ambiguity grows with the subject would raise a
polynomial to a power of n, and no bound of the shape in section 2 has that
form. That is the checker's `CrAmbiguous`, and it is what `(?:a*)*` gets.

How many times the head is reached, per entry, is `S`:

- The iteration count is `max(rep.lo, rep.hi)` when the repetition is bounded
  above. When it is not, the empty-match rule bounds it instead: past the
  minimum count, an iteration that consumed nothing is the last one, so all but
  the first `rep.lo` iterations eat at least one byte, and the count is
  `rep.lo + n + 1`.
- What the head is reached is one more than that, `K`. The head is where the
  counter is read, so the pass that finds the count spent is a pass of its own:
  it reads, decides, and leaves without entering the body. `a{2,5}` on five
  bytes reaches the head six times, with the counter at 0, 1, 2, 3, 4 and 5.
- Sort the passes by what the counter reads, which is a number from 0 to K-1
  and never repeats within a chain. Each iteration hands the next one `w`
  flows, so there are at most `w^i` passes at counter value `i` and

      S = w^0 + w^1 + ... + w^(K-1)

  That is `K` when `w <= 1`. When `w` is 2 or more the sum is
  `(w^K - 1) / (w - 1)`, which is at most `w^K`, and taking `w^K` is what the
  checker does. Bounded above, `w^K` is a constant. Unbounded, it is
  `w^(rep.lo+2) * w^n` — which is exactly where a base above 1 comes from.

Then, per entry:

    work  = 1 + S * (2 + b.work + w)
    stack = S * (1 + b.stack)
    trail = 1 + S * (1 + w + b.trail)
    outs  = S * (1 + w)

Reading the terms: the `1` outside is `RepZero`, once. Per pass through the
head there is the head itself and one `RepEnter`, the body, and one `RepNext`
per way the body finished. The head forks at most once per pass. The trail
takes `RepZero` once, then one `RepEnter` and `w` `RepNext` writes per pass.
Control leaves at the head, when the count is spent, and at the tail, when an
empty iteration ends the loop.

## 5. The whole call

The tree prices one entry into the program. A call is more than that.

With `ncap` capturing groups and `nregs` registers, the ovector holds
`novec = 2*(ncap+1)` slots and

    setup   = (nregs + novec) * 4      zeroed once, charged as cost and as memory
    deliver = novec * 4                copied back out once, on a match
    reset   = nregs * 4                cleared again at each starting position

There are at most `n + 1` starting positions. The bumpalong rule of
DESIGN.md section 4.3 can skip one, never add one.

The backtrack stack and the undo trail grow by doubling from four and are never
shrunk, so a run that holds at most `x` entries reserves at most `4 + 2x` of
them, and one that never pushes never allocates at all:

    capacity(x) = 0 if x is zero, else 4 + 2x

Peaks are per attempt: both arrays are truncated at every starting position, so
the root region's `stack` and `trail` are already the deepest either gets.
Capacity, on the other hand, is not given back, so growth is charged once
across the call rather than once per attempt. Summing the growth schedule, the
buffers allocated come to at most twice the final capacity and the buffers
copied out of to at most one more, so three times the final reservation covers
every byte the growth charged as cost. Momentarily holding both buffers is what
makes the memory peak twice the reservation rather than once.

    scratch = 12 * capacity(root.stack) + 8 * capacity(root.trail)

    cost  = setup + deliver
          + (n+1) * (reset + root.work + 4 * root.trail)
          + 3 * scratch
    stack = root.stack
    trail = root.trail
    mem   = setup + deliver + 2 * scratch

12 and 8 are `BT_SIZE` and `UNDO_SIZE`, the IR bytes of one backtrack entry and
one undo entry. `deliver` appears in the memory line as well as the cost one
because the delivered answer is resident: a caller holds the copied-out
ovector alongside the scratch, and a preallocated context materializes that
store at creation, in the result view its match calls answer through.

`cost`, `stack` and `mem` are the certificate's bounds the accessors report.
They are deliberately not the root region's numbers: a reader who found the
whole-pattern cost sitting on the root would have no way to tell that setup
and the attempt loop had been counted. The certificate's `trail` is the
fourth, never an accessor's answer: it is there because a preallocated
context sizes its undo array from the whole-pattern claim, exactly as it
sizes its backtrack array from `stack`.

Two of the four are held to their equations exactly. `cost` and `mem` are
bounds, and a certificate that claims more than the rules produce is
overestimating, which is its right. The `stack` and `trail` lines are
equalities: the memory requirement above is priced from the root region's
claimed numbers, and a preallocated context sizes its two arrays from the
whole-pattern claims, so any daylight between a claim and the walk would
demand an array the memory number never paid for. The checker refuses the
daylight rather than reasoning about it.

## 6. Classification

A certificate that calls itself linear is claiming its cost is at most
`c * (n + 1)`, so its cost bound must have base 1 and no power above the first.
Everything else is `notProvenLinear`, which is the honest contract of
DESIGN.md section 5: the bound may overestimate, never underestimate.

## 7. What the checker refuses

In the order it decides them, near enough:

```text
+----------------+--------------------------------------------------------+
| CrNoRules      | this configuration has no rules yet: memo, until M9    |
| CrConfig       | the certificate is for another configuration           |
| CrPrices       | one price per region, and this is not that             |
| CrNoRegions .. | the tree is not a tree, or its ranges do not nest      |
| CrOverlap      |                                                        |
| CrBase         | a claimed bound names a growth base of zero            |
| CrOpcode       | an instruction no region explains                      |
| CrShape        | the code, or a field, is not a shape the checker knows |
| CrChildren     | the children that kind requires are not the ones there |
| CrAmbiguous    | a repeat body whose ambiguity grows with the subject   |
| CrOverflow     | the requirement itself is past counter arithmetic      |
| CrRegion*      | a region claims less than its own rule produced        |
| CrTotal*       | the pattern claims less than section 5 produced — or,  |
|                | for the stack and the trail, anything but exactly it   |
| CrNotLinear    | the class claim does not match the shape of the bound  |
+----------------+--------------------------------------------------------+
```

`CrOk` means: for this program, in this configuration, at every subject length,
every start offset and every combination of match options, the matcher charges
no more cost, pushes no more backtrack entries and reserves no more scratch
than this certificate names.

## 8. What the analyzer answers

Three refusals and a certificate, and the difference between the refusals is
the difference between an inability and a bug:

```text
+----------------+--------------------------------------------------------+
| ArAmbiguous    | a repeat body whose ambiguity grows with the subject   |
| ArOverflow     | a coefficient, a power or a pass count with no room    |
| ArShape        | something in the tree the analyzer had no rule for     |
| ArOk           | a certificate, which the checker still has to accept   |
+----------------+--------------------------------------------------------+
```

The first two are the honest "no bound of the shape section 2 writes down".
The pattern compiles, carries no certificate, and the accessors report
ExceedsBudget for it. `(?:a*)*` is the first, `a*b*c*d*` and `(?:a|a){0,44}`
are the second at the two different places arithmetic runs out.

`ArOk` says a price came out, not that the tree was worth pricing. The analyzer
stops only where it would otherwise have to guess or read past the end of the
program; every rule in section 4 that holds a tree to the bytecode belongs to
the checker, and stating them twice would be the duplication this split exists
to avoid. So a tree that does not describe its own program may well price here
and be refused there.

That refusal, and `ArShape`, are the same thing: the two halves of this
document disagreeing about one program, which no pattern can cause and only a
bug of ours can. Compilation reports it rather than quietly dropping a bound.

## 9. The Pike configuration

The lockstep matcher does different work, so it gets its own accounting, and
the shape of that accounting is different too. The backtracking rules compose
prices over the region tree because the work a construct causes depends on
what surrounds it. In the Pike VM it does not: the visited set admits every
instruction at most once per list build, whatever the pattern's structure, so
the whole call has a closed form in a handful of counts read straight off the
program. A `CfgPike` certificate therefore carries no region prices — its
`prices` table is empty, and a checker met with a nonempty one refuses — and
its bounds are checked by recomputing the same closed form, cost and memory
by domination and the stack and the trail by the section 5 equalities — which
here are equalities with zero, coefficient by coefficient, since neither
array exists on this path.

The counts, for a program of `C` instructions:

    V = 2 * (ncap + 1)          capture slots in one block
    B = 4 * V                   IR bytes of one block, and of the ovector
    W = floor(C / 8) + 1        bytes of the per-position visited set
    S = OpSave instructions     the most copy-on-write can trigger per build

What one position costs. Building one thread list expands the closure: each
instruction is marked and charged at most once, so the marks are at most `C`.
Each `OpSave` processed can force at most one copy-on-write, at `B` cost
units; there are at most `S` of them per build. Stepping the finished list
charges one unit per suspended thread, and threads are deduplicated by pc, so
at most `C`; an accepting thread writes the match end through the same
copy-on-write, one more `B`. Seeding fills one fresh block, `B`, and clearing
the visited set is `W`. A pop the visited set turns away is not charged — it
does no instruction's work — and there are at most two per mark plus one per
suspended thread, so the uncharged bookkeeping stays a constant factor of the
charged work and the interpreter's fuel derivation holds.

    position = 2*C + (S + 2) * B + W

What the scratch reserves. Both thread lists hold at most `C` entries of 8
IR bytes; the closure stack at most `2*C`, since each mark pushes at most two
continuations; and every live capture handle sits in a list, on the closure
stack, or is the recorded match or the seed in flight, so the pool never
holds more than `4*C + 2` blocks, with a refcount and a free-list slot each.
Every one of these grows by the schedule of section 5, so with
`capacity(x) = 0 if x is zero, else 4 + 2x`:

    R = 8*capacity(C) * 2               the two thread lists
      + 8*capacity(2*C)                 the closure stack
      + 4*capacity(4*C + 2) * 2         refcounts and the free list
      + 4*capacity((4*C + 2) * V)       the pool
    setup = B + W                       the ovector and the visited set, zeroed once

And the whole call, with `n + 1` starting positions, growth charged at most
three times the reservation and holding at most twice of it at a peak, by the
same argument section 5 makes:

    cost  = setup + B + (n + 1) * position + 3*R
    stack = 0
    trail = 0
    mem   = setup + B + 2*R

`stack` and `trail` are zero because neither array exists on this path: the
stack-entry limit has nothing to refuse, and a certificate claiming entries
on either is refused instead. The extra `B` in both lines is the delivered
answer — copied out once as cost, resident alongside the scratch as memory,
for the same reason `deliver` sits in both section 5 lines. `mem` does not depend on `n` at all, which is the number
a context sizes once; `cost` is `c1 * (n + 1) + c0` with base 1 and nothing
above the first power, so every accepted `CfgPike` certificate claims
`CcLinear` and the checker requires exactly that — here linearity is the
shape of the rule, not a property to be read off the bound.

These are deliberately generous per-position counts — most builds mark far
fewer than `C` instructions — and the honest direction is the same as
everywhere else in this document: the bound may overestimate, never
underestimate. What keeps it meaningful is that every term is a compile-time
constant of the pattern, so the whole thing is one multiplication away from a
budget at any subject length.

A certificate for `CfgPike` is only accepted for a program `pike_ok` admits:
every repetition a pure star whose body cannot complete emptily, and nothing
that consumes a variable number of bytes. On such a program the four Rep
opcodes are control flow only, which is what lets the closure treat them as
epsilon forks, and the non-consuming transition graph is acyclic, which is
what makes first arrival at a pc the backtracking preference order and the
per-build mark count at most `C`.
