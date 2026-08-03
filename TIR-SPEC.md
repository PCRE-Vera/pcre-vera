# TIR — the normative specification

TIR ("trusted IR") is the small typed imperative language the pcre-truste
engine is written in. This document defines it: every type, every operator,
every statement, the exact result of every operation on every input, and the
rules a validator enforces before a program is accepted.

It is normative. Four independent implementations read it — the Python
reference interpreter, the Lean decoder and definitional interpreter, the Go
printer, and the JavaScript printer — and any corner left to taste here becomes
a divergence between them that testing finds much later, if at all. So where
Go and JavaScript disagree, this document picks one answer and both backends
implement it, even when that costs a helper function.

DESIGN.md sections 3 and 7 defer to this document. Where they sketch and this
one decides, this one wins; where this one is silent, that is a defect to be
reported, not a licence to improvise.

Version 1 of the language. The artifact carries `"tir": 1`; a change that
would alter the meaning of any accepted program bumps that number.

## Contents

```
+-----+---------------------------------------------------------------------+
|  1  | Overview and terminology                                            |
|  2  | Programs and declarations                                           |
|  3  | Types                                                               |
|  4  | Values, zero values, and storage sizes                              |
|  5  | Constants                                                           |
|  6  | Expressions                                                         |
|  7  | Places                                                              |
|  8  | Statements                                                          |
|  9  | Functions and calls                                                 |
| 10  | Linearity, freeze, take and swap                                    |
| 11  | Sequences: growth, capacity, and the byte ceiling                   |
| 12  | Traps                                                               |
| 13  | Evaluation order and failure ordering                               |
| 14  | Canonical JSON serialization                                        |
| 15  | Validator rules                                                     |
| 16  | Backend lowering requirements                                       |
+-----+---------------------------------------------------------------------+
```

## 1. Overview and terminology

A TIR program is a set of enum, struct, constant and function declarations. A
function has parameters, a body of statements, and at most one return value.
There is no recursion: the call graph is acyclic, so the host stack depth of
any generated function is a static constant and the only stacks that grow with
input are arrays the engine manages itself.

Two properties shape everything else.

**Expressions are pure.** An expression reads memory and computes; it never
writes, never calls a function, never allocates. All effects are statements.
This is why the evaluation-order rules of section 13 are short: the only thing
an expression can do out of order is *trap*, so ordering is observable exactly
at the trap boundary and nowhere else.

**Expressions are total, except for traps.** Every operator has a defined
result on every input of its operand types. Division by zero has an answer
because the author supplies one. Overflow has an answer because wrapping and
saturation are defined. The only way an expression fails is a checked access
that is out of range, and that is a trap (section 12), which stops the whole
engine call rather than producing a value.

Terminology used throughout:

- *scalar*: `bool`, `u8`, `i32`, `u32`, `counter`, or an enum type.
- *sequence*: `bytes` or a `vec` type.
- *copyable* and *linear*: section 3.3.
- *place*: something that can be written — a variable, a struct field, or an
  element of a sequence (section 7).
- *trap*: the defined failure of a checked operation (section 12).
- CAP: the counter saturation point, 2^53 - 1 = 9007199254740991.
- CEILING: the portable allocation ceiling, 2^31 - 1 = 2147483647 IR bytes,
  inclusive.

## 2. Programs and declarations

A program is a JSON object:

```json
{
  "tir": 1,
  "enums": [],
  "structs": [],
  "consts": [],
  "funcs": []
}
```

All five members are required; the four lists may be empty. `tir` must be the
integer 1 (rule V-001). Every name a type, expression or statement refers to
must be declared somewhere in the program (rule V-003).

The forms this document defines are all the forms there are (rule V-042): a
statement where a statement belongs, an expression where an expression
belongs, a place where a place belongs, one of section 3.1's types where a
type belongs, and a list of the right thing wherever a list belongs. The
reader gets this for free, since it only builds what it recognizes. The
validator checks it as well, and checks it first, because a program assembled
in memory never went through the reader, and the validator is meant to be the
boundary either way. Every rule below is written for a program that already
satisfies V-042.

An identifier matches `[A-Za-z_][A-Za-z0-9_]*` and is at most 64 characters
long (rule V-041). Identifiers are compared by exact byte equality; there is
no case folding and no normalization. Both the reader and the validator
enforce this, because a program that never went through the reader would
otherwise validate and then fail to re-read, which would make validation a
weaker statement than it looks.

**Reserved names.** The printers emit TIR names verbatim, so a name a target
language cannot spell, or one that would shadow something the generated scope
already needs, is refused here rather than mangled (rule V-043). TIR does not
define a mangling scheme on purpose: two printers would have to reproduce one
identically, and "refuse the case" is the same answer this document gives to
out-of-range shift counts. Refusing here rather than in a printer is what
makes validation the boundary it claims to be: a program that validates
prints, in every target, and a printer's own check of the same thing is
defense in depth rather than a second gate.

The reserved set is Go's keywords and predeclared identifiers, plus
JavaScript's reserved words including the strict-mode and future-reserved
ones, plus the two names Go can spell but cannot use: `_`, which names nothing
that can be referred to, and `init`, which at package level may only ever be a
function nothing is allowed to call.

The capitalized entries are the rest of what the generated scope holds. A
JavaScript module that lowers a multiplication reads `Math.imul`, and a
sequence reads `Uint8Array`, `Int32Array`, `Uint32Array`, `Float64Array`,
`Array` and `Error`; a TIR name printed verbatim into module scope would
shadow any of them, and a *parameter* shadows one just as thoroughly as a
function would. `ArtifactSHA256` and `artifactSha256` are the constants each
printer stamps the artifact's hash into (section 16). All of these are
printer-owned and versioned with this document, which is what separates them
from the hand-written wrapper's names: those live in a different scope on
purpose, so that this list never has to grow to cover them.

```
Array ArtifactSHA256 Error Float64Array Int32Array Math Uint32Array
Uint8Array _ any append arguments artifactSha256 await bool break byte cap
case catch chan class clear close comparable complex complex128 complex64
const continue copy debugger default defer delete do else enum error eval
export extends fallthrough false finally float32 float64 for func function
go goto if imag implements import in init instanceof int int16 int32 int64
int8 interface iota len let make map max min new nil null package panic
print println private protected public range real recover return rune select
static string struct super switch this throw true try type typeof uint
uint16 uint32 uint64 uint8 uintptr var void while with yield
```

No name may begin with `tir_` or `Tir_` either. The first belongs to the
helpers the printers generate. The second belongs to the exported façade the
Go printer has to emit, because Go cannot reach a lower-case name from another
package and TIR names go out verbatim; it is a second prefix rather than a
case-insensitive test because identifiers here compare by exact byte equality.
Adding a target language means adding its words to this list, which is a
deliberate, documented compatibility change like a pcre2 or Unicode bump.

**One top-level namespace.** Every enum name, enum *variant*, struct,
constant and function name lives in one namespace and they must be pairwise
distinct (rule V-002). Go and JavaScript
both put these in one scope when printed, so a program that distinguishes an
enum `Op` from a function `Op` cannot be printed to either language honestly.
Variants are in the same namespace for the same reason and not a weaker one: a
variant becomes a package-level typed constant in Go and a module-level
constant in JavaScript, so two enums that both spell a variant `Add` produce
two declarations of `Add` in one scope. Section 16 is what keeps that scope
free of anything else.

**No shadowing anywhere.** Within a function, every parameter and every local
introduced by a `let` must have a name distinct from all other parameters and
locals of that function *and* from every top-level name (rule V-038). Scoping
then never
affects which declaration a name refers to; it only affects lifetime
(section 8.1).

**Nothing nests more than 64 deep.** Depth is counted from a function's body:
a statement directly in it is at depth 1, and anything inside a construct is
one deeper — a statement in its block, an expression in its condition, an
operand of that expression, a place under an assignment, a value inside a
constant. Two chains through the declarations are measured the same way and
against the same number: a struct that contains a struct that contains
another, and a path through the call graph. None of the five may exceed 64
(rule V-044).

The number is a real limit rather than a courtesy. A printer emits nesting
verbatim, so a TIR expression nested three hundred deep becomes a Go or
JavaScript expression nested three hundred deep, and both languages' compilers
have their own quiet limits there. A decoder recurses to read it, a printer to
write it, and this document's own reference interpreter to run it. Bounding
the two declaration chains is what bounds those walks in turn: linearity, the
storage size and the zero value are each defined by recursion over struct
containment, and a call is a stack frame. Sixty-four is far past anything an
author writing an engine reaches, and far short of what any of the
implementations would struggle with — which is the whole point of picking one.

Declaration order in the artifact is the canonical order defined in section
14: each list is sorted by name. Order carries no meaning — a function may
call one declared after it, as long as the call graph stays acyclic.

### 2.1 Enums

```json
{"name": "Phase", "variants": ["Enter", "Left", "Right"]}
```

An enum is a C-like tag set. It must declare at least one variant, and variant
names must be distinct within the enum (rule V-004) — and, per section 2's one
namespace, distinct from every other name the program declares, variants of
other enums included (rule V-002). Naming a variant an enum does not have is a
resolution failure like any other, so it is V-003, wherever it happens — in an
expression or in a constant.

The *ordinal* of a variant is its index in the declared list, starting at 0.
Ordinals are observable: they fix the zero value (section 4.1) and the integer
constants a backend emits. Reordering the variant list is therefore a
semantic change, not a cosmetic one. Note that the canonical serializer sorts
*declarations* by name but never the variant list, which is the declaration.

### 2.2 Structs

```json
{"name": "Frame", "fields": [{"name": "pc", "type": "u32"},
                             {"name": "phase", "type": {"enum": "Phase"}}]}
```

A struct declares at least one field; field names must be distinct within the
struct (rule V-005). Field order is the declared order and is observable through the
storage layout of section 4.2, so it too is a declaration rather than a
presentation detail and is never sorted.

Struct definitions must not be recursive, directly or through other structs
(rule V-005 again). A recursive struct has no finite storage size and no zero
value.

### 2.3 Constants and functions

Constants are section 5, functions section 9.

## 3. Types

### 3.1 The type grammar

A type is one of:

```
"bool"                                  the two truth values
"u8"                                    integers 0 .. 255
"i32"                                   integers -2^31 .. 2^31 - 1
"u32"                                   integers 0 .. 2^32 - 1
"counter"                               integers 0 .. CAP, saturating
"bytes"                                 a growable sequence of u8
{"enum": "Name"}                        a declared enum
{"struct": "Name"}                      a declared struct
{"vec": {"elem": T, "max": N}}          a growable sequence of T
{"frozen": T}                           an immutable, shareable T
```

Two types are equal when their JSON representations are equal after
canonicalization. A `vec` with a different `max` is a different type: the
declared maximum is part of what the type promises, so it cannot be lost by
assignment.

There are deliberately no 64-bit integers. JavaScript numbers cannot represent
them exactly and BigInt is too slow for the matcher's inner loop. Everything
that needs to count past 2^32 uses `counter`, which saturates at CAP and is
therefore exact in a double.

### 3.2 `bytes` and `vec<u8, N>`

`bytes` is a sequence type with element type `u8` and declared maximum
CEILING. It behaves exactly as `{"vec": {"elem": "u8", "max": 2147483647}}`
would, which is why that spelling is rejected by the validator (rule V-010):
one meaning, one spelling. `bytes` exists as its own type because the backends
give it its own storage — `[]byte` in Go, `Uint8Array` in JavaScript — and
because it is the shape a pattern and a subject arrive in.

`vec` of `u8` with a smaller maximum is a perfectly ordinary vec and is what a
bounded byte table should use.

### 3.3 Copyable and linear types

A type is *linear* when a value of it is backed by storage that could be
aliased if it were copied. Linearity is what lets the semantics say there is
no aliasing at all, instead of reasoning about when a copy is safe.

```
linear:   bytes, vec<T, N>, and any struct with at least one linear field
copyable: everything else — bool, u8, i32, u32, counter, enum,
          frozen<T>, and structs all of whose fields are copyable
```

The rules that follow from this are section 10.

### 3.4 Frozen types

`{"frozen": T}` is legal only when `T` is linear (rule V-008), and never
nests: `frozen<frozen<T>>` is rejected (rule V-009). A frozen value is
permanently immutable, so aliasing it is invisible to the semantics, so it is
copyable. That is the one escape from linearity, and it is one-way: nothing
turns a `frozen<T>` back into a `T` except an explicit deep copy, which
produces a new value.

Reading through a frozen value gives frozen results where the result would
otherwise be linear:

```
field of frozen<S> named f, where S.f has type F
    -> frozen<F> if F is linear, F otherwise
element of frozen<vec<T, N>>  -> T          (T is always copyable, rule V-006)
element of frozen<bytes>      -> u8
```

### 3.5 Element and field restrictions

The element type of a `vec` must be copyable (rule V-006). A sequence of
sequences would put heap-backed values inside heap-backed values, which
multiplies the ownership rules by themselves for no gain: the engine's own
data structures are flat arenas of scalar structs indexed by `u32`, which is
what this restriction encodes. A struct field, on the other hand, may have any
type; a struct holding a `vec` is simply linear.

## 4. Values, zero values, and storage sizes

### 4.1 Zero values

Every type has a zero value. It is what a `let` without an initializer
produces, what `take` leaves behind, and what the engine's own reset paths
write.

```
bool            false
u8, i32, u32    0
counter         0
enum E          the variant with ordinal 0
struct S        every field at its own zero value
vec, bytes      length 0, capacity 0
frozen<T>       a frozen value equal to the zero value of T
```

The zero value of an enum is the *first declared* variant. An author who wants
a particular variant to be the zero declares it first.

### 4.2 IR storage sizes

Storage sizes are an engine-defined unit, used by the section 5 memory
accounting of DESIGN.md and by the capacity derivation below. They are not a
promise about what a host allocates; Go and JavaScript object layout is not
ours to guarantee, and each backend documents its own real cost separately.
What matters is that all four implementations compute the *same* numbers.

```
sizeof(bool)        = 1
sizeof(u8)          = 1
sizeof(i32)         = 4
sizeof(u32)         = 4
sizeof(counter)     = 8
sizeof(enum E)      = 4
sizeof(bytes)       = 8      the handle; the elements are counted separately
sizeof(vec<T, N>)   = 8      likewise
sizeof(frozen<T>)   = 8      likewise
sizeof(struct S)    = the sum of sizeof over its fields, in declared order
```

Structs are packed: no alignment, no padding, no reordering. A real Go struct
will be larger and a JavaScript object larger still, and both backends say so
in their own documentation. `sizeof` is the unit the bounds are stated in, and
its value is that it is the same everywhere.

The *backing storage* of a sequence with capacity `c` and element type `T` is
`c * sizeof(T)` IR bytes. The handle counted by `sizeof` above is separate and
covers only the value that sits in a variable, field, or element.

## 5. Constants

```json
{"name": "BITS", "type": {"frozen": "bytes"}, "value": {"bytes": "0102040810204080"}}
```

A constant has a name, a type, and a value. Its type must be a scalar, an
enum, or a frozen type (rule V-011): a constant is shared by every function
that reads it, and sharing is exactly what `frozen` licenses. A linear
constant would be a contradiction.

Constant values are written as:

```
bool               true / false
u8, i32, u32       an integer in the type's range
counter            an integer in 0 .. CAP
enum E             {"variant": "Name"}
struct S           {"fields": {"name": value, ...}}, every field exactly once
bytes              {"bytes": "<lowercase hex, even length>"}
vec<T, N>          {"elems": [value, ...]}, at most N of them
frozen<T>          the value of T
```

A value that does not match its declared type in every one of those respects
is rejected (rule V-012). A constant sequence has capacity equal to its
length.

Constants are referenced from expressions with `{"constref": "NAME"}`. There
is no way to write to one: a constant reference is an expression, not a place.

## 6. Expressions

Every expression node is a one-key JSON object. Its type is determined by the
node and its operands; there is no inference and no implicit conversion
anywhere in TIR. A `u8` never becomes a `u32` without a `cast`. An expression
whose operand types do not fit the operator, or do not match each other where
the operator says they must, is rejected (rule V-013).

Each operator list below is closed. An operator name that is not on its list
is not "an operator this document forgot", it is rejected — by the reader,
which has never heard of it, and again by the validator, since a program built
without going through the reader has to meet the same bar.

### 6.1 Literals

```json
{"bool": true}    {"u8": 255}    {"i32": -2147483648}
{"u32": 4294967295}    {"counter": 9007199254740991}
```

The value must be in the range of the named type (rule V-014). There are no
untyped literals: `{"u32": 7}` and `{"i32": 7}` are different expressions of
different types, which is what makes the operand-type rules below decidable
without inference.

### 6.2 Variables and constants

```json
{"var": "name"}         a parameter or local, of its declared type
{"constref": "NAME"}    a declared constant, of its declared type
```

A linear value never *evaluates to* anything: it moves. So an expression whose
type is linear may appear in exactly two positions, and nowhere else
(rule V-023):

- as the base of a `field`, `index`, `len` or `cap`. Projecting is not reading:
  `len(s.scratch)` asks a question about a vec without producing one, and
  `s.pc` reads a copyable field out of a struct that happens to hold a vec.
  What matters is the type of the *result*, not of the base.
- as the `src` of `copy`, which is the sanctioned duplication and is deep.

Anywhere a value is actually consumed — an assignment's right-hand side, an
`in` argument, a pushed element, a returned value, an operand — a linear type
is rejected.

### 6.3 Field access

```json
{"field": {"base": Expr, "name": "pc"}}
```

`base` must have struct type or `frozen<struct>`, and `name` must be one of
its fields. The result type follows section 3.4. Field access never fails.

### 6.4 Indexing

```json
{"index": {"base": Expr, "index": Expr}}
```

`base` must be a sequence or a frozen sequence; `index` must have type `u32`.
The result is the element at that position: `u8` for `bytes`, the element type
for a `vec`.

Indexing is *checked*. If `index >= len(base)` the operation traps (section
12). This is the only expression form that can fail, and it is why evaluation
order is observable at all.

### 6.5 Length and capacity

```json
{"len": Expr}    {"cap": Expr}
```

`Expr` must be a sequence or a frozen sequence. Both return `u32`. `len` is
the number of elements, `cap` the current capacity; section 11 defines exactly
how capacity moves, so `cap` is deterministic and may be relied on.

### 6.6 Unary operators

```json
{"un": {"op": "not" | "neg" | "bnot", "arg": Expr}}
```

```
+--------+-----------------+----------------------------------------------+
| op     | operand type    | result                                       |
+--------+-----------------+----------------------------------------------+
| not    | bool            | the other truth value                        |
| neg    | u8, i32, u32    | (0 - x) mod 2^w, read back in the type       |
| bnot   | u8, i32, u32    | (2^w - 1 - x') where x' is the unsigned      |
|        |                 | reading of x, read back in the type          |
+--------+-----------------+----------------------------------------------+
```

`w` is the width in bits: 8 for `u8`, 32 for `i32` and `u32`. "Read back in
the type" means: for `u8` and `u32` the result is that residue; for `i32` the
residue is interpreted as two's complement, so residues at or above 2^31 have
2^32 subtracted.

`neg` on `i32` of -2147483648 is -2147483648. That is a wrap, not an error;
TIR has no signed-overflow trap.

There is no `neg` or `bnot` on `counter`: `counter` is unsigned and saturating,
and both operators would only produce a value the type does not mean.

### 6.7 Wrapping and saturating arithmetic

```json
{"bin": {"op": "add" | "sub" | "mul", "left": Expr, "right": Expr}}
```

Both operands must have the same type, one of `u8`, `i32`, `u32`, `counter`.

On `u8`, `i32` and `u32` the result is the exact mathematical result reduced
mod 2^w and read back in the type, as in section 6.6. This is two's-complement
wrapping and it never fails.

On `counter` the operations *saturate*, and the check happens before the
arithmetic:

```
add(a, b) = if a > CAP - b then CAP else a + b
sub(a, b) = if a < b       then 0   else a - b
mul(a, b) = if a = 0 or b = 0 then 0
            else if a > CAP div b then CAP
            else a * b
```

`div` here is exact integer division rounding down. Every counter value is in
`0 .. CAP` by construction, so `CAP - b` and `CAP div b` are themselves in
range and the pre-checks never overflow.

Why the pre-check rather than the obvious "add, then clamp": in JavaScript a
counter is a plain double, and an unchecked product of two large counters
rounds before any comparison can look at it. The pre-check form is exact in
every target — this is worth stating precisely, because a reader has to be
able to check it:

- `CAP - b` is an integer in `0 .. CAP`, hence exactly representable, and
  IEEE subtraction of two exactly-representable integers whose difference is
  exactly representable is exact.
- `Math.floor(CAP / b)` equals the true floor for every `b` in `1 .. CAP`.
  Write `q = CAP / b` and `N = floor(q) + 1`. Since `N * b` and `CAP` are
  integers with `N * b > CAP`, we have `N * b - CAP >= 1`, so
  `N - q >= 1/b = q/CAP > q * 2^-53`, which is at least the half-ulp of `q`.
  Rounding to nearest therefore cannot reach `N`, and it cannot fall below
  `floor(q)` either, since `floor(q)` is itself representable. So the floor of
  the rounded quotient is the floor of the true quotient.
- When the pre-check passes, the true result is at most CAP, hence exactly
  representable, so the addition or multiplication that follows is exact.

Go computes counters in `uint64`, where the same formulas are exact for the
same reason and cheaper to see.

### 6.8 Bitwise operators

```json
{"bin": {"op": "and" | "or" | "xor", "left": Expr, "right": Expr}}
```

Operands must have the same type, one of `u8`, `i32`, `u32`. The operation is
performed on the two's-complement bit patterns of width `w` and the result is
read back in the type. There are no bitwise operators on `bool` — that is what
section 6.11 is for — and none on `counter`, whose value is a count rather
than a bit pattern.

### 6.9 Checked division and remainder

```json
{"div": {"left": Expr, "right": Expr, "fallback": Expr}}
{"rem": {"left": Expr, "right": Expr, "fallback": Expr}}
```

All three operands must have the same type, one of `u8`, `i32`, `u32`,
`counter`. Division and remainder are the two arithmetic operations with a
genuinely undefined case, so TIR does not let an author leave it open: the
third operand says what a zero divisor yields, at the point where the author
knows what it should mean.

```
div(a, b, f) = f                       if b = 0
             = trunc(a / b)            otherwise
rem(a, b, f) = f                       if b = 0
             = a - b * trunc(a / b)    otherwise
```

`trunc` rounds toward zero, which only differs from rounding down for `i32`.
On `u8`, `u32` and `counter` all values are non-negative and the two agree.
The sign of a remainder is the sign of the dividend: `rem(-7, 2, f) = -1`.

Two `i32` cases deserve to be named, because both are hardware traps in C and
a runtime panic in Go:

```
div(-2147483648, -1, f) = -2147483648      the wrapping result, no trap
rem(-2147483648, -1, f) = 0
```

The `fallback` operand is always evaluated, in the left-to-right order of
section 13, whether or not the divisor turns out to be zero. It is an
expression like any other, so evaluating it costs nothing beyond its own
reads, and making it conditional would put a second short-circuit rule in the
language for no benefit.

### 6.10 Shifts

```json
{"shift": {"op": "shl" | "shr" | "sar", "arg": Expr, "count": 3}}
```

`count` is a JSON integer literal, not an expression. It must be in
`0 .. w - 1` for the width `w` of the operand type (rule V-015).

```
+-----+-----------------+-------------------------------------------------+
| op  | operand type    | result                                          |
+-----+-----------------+-------------------------------------------------+
| shl | u8, i32, u32    | (x * 2^count) mod 2^w, read back in the type    |
| shr | u8, u32         | floor(x / 2^count), a logical shift             |
| sar | i32             | floor(x / 2^count) over the signed value, so    |
|     |                 | the sign bit propagates                         |
+-----+-----------------+-------------------------------------------------+
```

`shr` on `i32` and `sar` on unsigned types are rejected rather than defined
(rule V-016). Both spellings exist precisely so that a reader never has to ask
which one an operand type implies.

A constant count is what "validator-enforced in-range count" means. Go and
JavaScript genuinely disagree about out-of-range counts — Go yields 0 for a
shift of 32, JavaScript masks the count to 5 bits and yields the operand — and
neither answer is more right than the other. Refusing to have the case at all
is cheaper than picking one and paying for it in every generated shift.

A variable shift is written as a table lookup. `1 << (b & 7)` becomes an index
into a 256-entry constant, which is what the engine's class bitmaps do anyway:

```json
{"index": {"base": {"constref": "BIT"}, "index": {"cast": {"type": "u32", "arg": {"var": "b"}}}}}
```

### 6.11 Comparisons

```json
{"cmp": {"op": "eq" | "ne" | "lt" | "le" | "gt" | "ge",
         "left": Expr, "right": Expr}}
```

Both operands must have the same type; the result is `bool`.

`eq` and `ne` accept `bool`, `u8`, `i32`, `u32`, `counter` and enum types. The
ordering comparisons accept `u8`, `i32`, `u32` and `counter` only: ordering
booleans is meaningless, and ordering enum variants would make the ordinal a
load-bearing part of every program that uses one.

`i32` compares as signed. `u8`, `u32` and `counter` compare as unsigned. There
is no comparison of sequences, structs, or frozen values; TIR has no
structural equality, and adding one would put a deep traversal behind an
innocuous-looking operator.

### 6.12 Boolean and / or

```json
{"and": {"left": Expr, "right": Expr}}
{"or": {"left": Expr, "right": Expr}}
```

Both operands must be `bool`, and the result is `bool`. These are defined as
conditionals, not as operators:

```
and(a, b) = if a then b else false
or (a, b) = if a then true else b
```

so the right operand is evaluated only when the left does not already settle
the answer. This is the *only* place in TIR where an operand may go
unevaluated. Since expressions are pure, the difference is observable only
through traps: `and(i < len(v), v[i] == 0)` is well defined and does not trap
when `i` is out of range, and that is exactly why the short circuit is written
into the semantics rather than left to a backend's operator table.

### 6.13 Casts

```json
{"cast": {"type": "u32", "arg": Expr}}
```

The target type must be `u8`, `i32`, `u32` or `counter`. The operand type must
be `bool`, `u8`, `i32`, `u32` or `counter`. Nothing else casts: there is no
cast to or from a sequence, struct, enum, or frozen type.

```
+-------------+-------------+-------------------------------------------+
| from        | to          | result                                    |
+-------------+-------------+-------------------------------------------+
| bool        | any integer | 0 for false, 1 for true                   |
| any integer | u8          | x mod 256                                 |
| any integer | u32         | x mod 2^32                                |
| any integer | i32         | x mod 2^32, read as two's complement      |
| u8, u32     | counter     | x, exactly; both ranges fit under CAP     |
| i32         | counter     | 0 if x < 0, otherwise x                   |
| counter     | u8/u32/i32  | as the mod rules above                    |
| T           | T           | the operand, unchanged                    |
+-------------+-------------+-------------------------------------------+
```

The `i32` to `counter` rule saturates at zero rather than reinterpreting,
because `counter` counts things and a negative count has no reading. An author
who wants the two's-complement value casts through `u32` first, which says so
out loud.

There is no cast to `bool`. Write the comparison: `{"cmp": {"op": "ne", ...}}`
against a zero literal.

### 6.14 Enum and struct literals

```json
{"enumval": {"type": "Phase", "variant": "Left"}}
{"structval": {"type": "Frame", "fields": {"pc": Expr, "phase": Expr}}}
```

A struct literal must give every field exactly once, and the struct type must
be copyable (rule V-017): a linear struct is built by assigning its fields, so
that the linear values inside it arrive by `take` or `call` rather than by
evaluation.

## 7. Places

A place denotes storage that can be written. The grammar is a subset of the
expression grammar:

```json
{"var": "name"}
{"field": {"base": Place, "name": "f"}}
{"index": {"base": Place, "index": Expr}}
```

The root of a place is always a variable: a local or a parameter, in scope
(rule V-039). That its projections exist — a field of that struct, an index
into a sequence — is a typing question like any other, so it is V-013. There
are no pointers, no addresses, and no place derived from a constant or from a
function result.

A place is *writable* when:

- its root is a local, or an `inout` parameter — an `in` parameter is
  immutable (rule V-025), so a function never quietly rewrites its own
  argument copy; and
- no prefix of its projection path has a frozen type (rule V-026).

Indexing a place is checked exactly as in section 6.4 and traps the same way.

The *access path* of a place is its root variable followed by its projections,
where each index projection records the literal index if the index expression
is an integer literal and "unknown" otherwise. Access paths are what section
9.2 compares for disjointness.

## 8. Statements

A body is a JSON array of statements. Each statement is a one-key object.

Statements after a `return`, `break` or `continue` in the same array are
rejected (rule V-027): unreachable code in a language this small is always a
mistake, and refusing it keeps every body's control-flow graph obvious.

### 8.1 let

```json
{"let": {"name": "i", "type": "u32", "init": Expr}}
```

Declares a variable, visible from this statement to the end of the enclosing
statement array. `init` may be `null`, in which case the variable starts at
the zero value of its type (section 4.1); a non-null initializer requires a
copyable type and an expression of exactly that type (rule V-037).

Names do not shadow (section 2), so the scope of a `let` only decides when the
variable exists, never which declaration a name means. Re-entering a block —
a loop body, say — re-initializes the variable.

### 8.2 assign

```json
{"assign": {"place": Place, "value": Expr}}
```

The place must be writable and the value's type must equal the place's type,
which must be copyable. Linear values move; see section 10.

### 8.3 take, swap, copy, freeze

These four statements are the whole of linear-value movement.

```json
{"take":   {"dest": Place, "src": Place}}
{"swap":   {"a": Place, "b": Place}}
{"copy":   {"dest": Place, "src": Expr}}
{"freeze": {"dest": Place, "src": Place}}
```

`take` moves the value at `src` into `dest` and leaves the zero value of the
type behind. Both places must have the same type and must be writable and
provably disjoint (rule V-028).

`swap` exchanges the values at two writable places of the same type, which
must be provably disjoint (rule V-029).

`copy` deep-copies. `src` may have type `T` or `frozen<T>`, `dest` must have
type `T`, and `T` may be any type at all — this is also how a copyable value
is duplicated out of a frozen container. Every *mutable* sequence the copy
reaches is a fresh one whose capacity equals its length; a frozen value inside
it is shared rather than duplicated, which is what freezing bought and what
keeps `cap` on it the same number afterwards. `dest` and `src` must be provably
disjoint (rule V-030).

`freeze` moves the value at `src`, which must have a linear type `T`, into
`dest` of type `frozen<T>`, and leaves the zero value of `T` at `src`. The
result is permanently immutable and may from then on be copied, passed by
value and shared. This is what lets one compiled pattern serve any number of
concurrent match calls while every mutable scratch value stays linear.

`take`, `swap` and `copy` apply to copyable types too, where `take` is a move
that also zeroes the source and `copy` is an ordinary assignment. Nothing
forces an author to use them there, and `assign` is the natural spelling.

### 8.4 Sequence statements

```json
{"push":     {"seq": Place, "value": Expr}}
{"pop":      {"seq": Place, "dest": Place}}
{"truncate": {"seq": Place, "len": Expr}}
{"reserve":  {"seq": Place, "cap": Expr}}
```

`seq` must be a writable place of sequence type — never a frozen one.

`push` appends. The value's type must be the element type. If the length is
already the declared maximum, it traps (section 12); otherwise capacity grows
if needed, by the schedule of section 11.

`pop` removes the last element and stores it in `dest`, whose type must be the
element type. It traps on an empty sequence. Capacity does not change.

`truncate` sets the length to `len`, a `u32`. It traps if `len` is greater
than the current length; shortening never reallocates, so capacity does not
change.

`reserve` raises the capacity to `cap`, a `u32`, if it is not already at least
that. It traps if `cap` exceeds the declared maximum. It never shrinks and
never changes the length.

In `push` and `pop` the sequence place and the value or destination place must
be provably disjoint (rule V-031).

### 8.5 if

```json
{"if": {"cond": Expr, "then": [Stmt], "else": [Stmt]}}
```

`cond` must be `bool`. `else` may be an empty array; it is always present in
the artifact.

### 8.6 while

```json
{"while": {"cond": Expr, "variant": Expr, "body": [Stmt]}}
```

`cond` must be `bool` and `variant` must have type `counter` (rule V-036).

The variant is the loop's termination argument: the claim that its value
strictly decreases from the start of one iteration to the start of the next.
The Lean side discharges that claim; the backends ignore the variant entirely
and print a plain loop; the Python reference interpreter *checks* it at
runtime and reports a violation rather than looping forever, which turns a
false variant into a failing test the first time the loop runs.

The variant is therefore not part of the program's observable behavior, and
this is worth saying out loud because it is exactly the kind of thing that
becomes a divergence. A variant that would trap — one that indexes past the
end of a sequence — is a defect in the program, not a TIR outcome: the
backends never evaluate it and so never see it, and the reference interpreter
reports it the same way it reports a variant that fails to decrease. Nothing
about the answer a program computes may depend on the variant.

### 8.7 switch

```json
{"switch": {"value": Expr,
            "arms": [{"variant": "Left", "body": [Stmt]}],
            "default": [Stmt]}}
```

`value` must have an enum type. Arm variants must belong to that enum and must
not repeat. Either the arms cover every variant and `default` is `null`, or
they do not and `default` is a body (rule V-032). A default that can never run
is dead code and is rejected on the same grounds as section 8's unreachable
statements.

Arms do not fall through. `break` inside a switch arm belongs to the enclosing
loop, not to the switch; a switch is not a breakable construct.

### 8.8 break, continue, return

```json
{"break": {}}    {"continue": {}}    {"return": {"value": Expr}}
```

`break` and `continue` must appear inside a `while` body (rule V-033), and
they refer to the innermost enclosing one.

`return` carries a value exactly when the function declares a return type, and
its type must match (rule V-034). Every path through a function that declares
a return type must end in a `return` (rule V-035); falling off the end is
rejected rather than given a default value.

### 8.9 call

```json
{"call": {"fn": "helper", "args": [{"in": Expr}, {"inout": Place}],
          "dest": Place}}
```

Section 9.

## 9. Functions and calls

```json
{"name": "step",
 "params": [{"name": "n", "type": "u32", "mode": "in"},
            {"name": "out", "type": "bytes", "mode": "inout"}],
 "ret": "bool",
 "body": [ ... ]}
```

`ret` is `null` for a function that returns nothing.

Parameter modes are `in` and `inout`, and nothing else (rule V-040). An `in`
parameter is passed by value and
is immutable inside the function; its type must be copyable (rule V-018), so
linear values never travel by value. An `inout` parameter is an alias for a
place at the call site; it may have any type, and it is the only way a
function receives a linear value or returns one.

A return type must be copyable (rule V-019). A function that produces a
sequence writes it through an `inout` parameter.

### 9.1 Calls

A call is a statement, never an expression. The call's `dest` is present
exactly when the callee declares a return type (rule V-020). Arguments must
match the parameter list in count, mode and type: an `in` parameter takes an
expression of that exact type, an `inout` parameter takes a writable place of
that exact type.

The call graph must be acyclic, self-calls included (rule V-021). TIR has no
recursion at all, which is what makes the host stack depth of every generated
function a static constant.

### 9.2 inout disjointness

At every call site, an `inout` argument's access path must be provably
disjoint from the access path of every other argument — `in` arguments
included, since they read — and from the `dest` place (rule V-022).

Two access paths are *provably disjoint* when, comparing their projections in
order after equal roots:

- different roots: disjoint. There is no aliasing between distinct variables,
  which is what linearity buys.
- a field projection with a different name: disjoint.
- two index projections with different literal indices: disjoint.
- two projections that agree — the same field name, or the same literal index —
  settle nothing on their own; the comparison moves on to the next pair, which
  is what makes `v[0].a` and `v[0].b` disjoint.
- an index projection where either side is not a literal: not provably
  disjoint, whatever the runtime values might be.
- one path exhausted while the other continues: not disjoint. A struct and one
  of its own fields overlap.

The paths compared for an argument are: for `{"inout": p}`, the path of `p`
plus the paths of every place read inside its index expressions; for
`{"in": e}`, the paths of every place `e` reads.

So `f(inout v, inout v)` is rejected, and so are `f(inout s, inout s.pc)`,
`f(inout v[0], inout v[i])`, and `f(inout i, in len(v[i]))`. `f(inout v[0],
inout v[1])` is accepted, because two literal indices settle it, and so is
`f(inout v[0].a, inout v[0].b)`, because the field names settle what the equal
indices left open.

Checking access paths rather than variable names is the point: names alone
would admit a struct and its own field as two `inout` arguments, which is
precisely the aliasing the rule exists to prevent.

## 10. Linearity, freeze, take and swap

Collecting the rules that section 3.3 sets up, because they are the ones an
author trips over:

1. A linear value is never consumed as a value (rule V-023, with the two
   positions section 6.2 allows). It moves, through `take`, `swap`, `copy`,
   `freeze`, or an `inout` argument.
2. A linear value is never assigned (rule V-024): `assign` requires a copyable
   type.
3. A linear type is never an `in` parameter (rule V-018), never a return type
   (rule V-019), never a `vec` element (rule V-006), and never a field of a
   struct that a struct literal builds (rule V-017).
4. Every linear value therefore has exactly one live name at any moment. There
   is no aliasing to reason about in Lean, and both backends can use their
   native reference types without the model lying about them.
5. `freeze` is the one-way escape. After it, the value is immutable and freely
   shareable, and a write through any frozen path is rejected statically
   (rule V-026).

The discipline covers access paths, not just whole variables. A linear struct
field or a sequence held in a field is read and written in place through its
projection, and moving one out of its container goes through `take`, which
leaves the zero value behind. That is what "take-or-swap" means in DESIGN.md
section 3.1.

## 11. Sequences: growth, capacity, and the byte ceiling

### 11.1 The ceiling and the derived capacity

One inclusive ceiling governs every allocation: CEILING = 2^31 - 1 IR bytes.
It is what every target can represent and address, and DESIGN.md section 2.4's
resource limits inherit it.

For a sequence with element type `T`, the maximum element capacity is

```
maxcap(T) = floor(CEILING / sizeof(T))
```

so a `{"vec": {"elem": T, "max": N}}` is well formed only when
`1 <= N <= maxcap(T)` (rule V-007). `bytes` has `sizeof(u8) = 1` and therefore
`maxcap = CEILING`, which is its declared maximum.

The declared maximum is a property of the type, not of a value: two vecs of
the same element type with different maxima are different types and neither is
assignable to the other.

### 11.2 The growth schedule

Growth must be identical in all four implementations, because DESIGN.md
section 5 counts peak allocated capacity and a backend with a different
doubling policy would report a different peak.

```
push onto a sequence of length L, capacity C, declared maximum N:
    if L = N                    trap
    if L < C                    capacity unchanged
    if L = C                    new capacity = min(N, max(4, 2 * C))

reserve to capacity R:
    if R > N                    trap
    if R <= C                   nothing happens
    otherwise                   new capacity = R exactly

truncate and pop                capacity unchanged
```

`reserve` sets the capacity exactly, with no rounding up: it is the operation
an author reaches for when the needed size is known, and rounding it would
make the sized-up-front path — which is how the matchers avoid growing at all
— less predictable than the growing one.

Since `L < N` whenever a push grows, and `max(4, 2 * C) > C` for every
`C >= 0`, the new capacity is always at least `L + 1`.

### 11.3 Growth and memory accounting

A growing sequence briefly holds both buffers: the old one is still live while
the elements are copied. DESIGN.md section 5 counts

```
(C_old + C_new) * sizeof(T)
```

IR bytes against the memory budget at that moment, which is why the peak is
what the accounting reports rather than the final capacity. Both backends
allocate a new buffer and copy; neither may use an in-place reallocation that
would make the peak smaller and the number wrong.

That accounting is the M5 analyzer's. What TIR fixes here, and what the
analyzer reads, is the schedule: given the sequence of operations a program
performs, the capacity after each one is determined, so the peak is a function
of the program rather than of an implementation's appetite.

## 12. Traps

A trap is the defined failure of a checked operation. It stops the engine call
immediately; there is no handler, no unwinding a TIR author can observe, and
no partial result. In the formal semantics it is a distinct outcome of running
a function, not a value.

The complete list:

```
+------+----------------------------------------------------------------+
| T-01 | index >= len, on a read or a write, on any sequence or frozen  |
|      | sequence                                                       |
| T-02 | pop from a sequence of length 0                                |
| T-03 | truncate to a length greater than the current length           |
| T-04 | reserve to a capacity greater than the declared maximum        |
| T-05 | push onto a sequence whose length is already the declared      |
|      | maximum                                                        |
+------+----------------------------------------------------------------+
```

That is all of them. Arithmetic never traps: wrapping, saturation, and the
`fallback` operand of `div` and `rem` between them define every case.

What a trap means, honestly stated. On the surface the Lean proofs cover,
every check is discharged and the trap is provably unreachable. On code the
proofs do not yet reach — a milestone still in flight, or a feature behind
`allowUnproved` — it is only *tested* unreachable, and DESIGN.md section 3.1
says so rather than rounding up. What the trap buys unconditionally is that an
engine bug fails immediately and visibly instead of reading a neighbouring
object: the backends must realize it (section 16), not assume it away.

## 13. Evaluation order and failure ordering

Evaluation is strictly left to right, in the order the operands are written.
Because expressions are pure, the only thing this decides is which trap fires
when more than one could — but that is a real observable, so it is pinned.

Within an expression:

```
{"bin"|"cmp"|"div"|"rem"}   left, then right, then fallback if present
{"index"}                   base, then index, then the bounds check
{"field"} {"len"} {"cap"}   the operand, then the operation
{"un"} {"cast"} {"shift"}   the operand, then the operation
{"structval"}               the fields in the struct's declared order
{"and"} {"or"}              left; right only if left does not settle it
```

Within a statement:

```
{"assign"}          the destination place (its index expressions left to
                    right, each bounds-checked as it is resolved), then the
                    value, then the store
{"take"} {"swap"}   the places in written order: dest then src, a then b
{"copy"}            dest, then src
{"freeze"}          dest, then src
{"push"}            the sequence place, then the value, then the append
{"pop"}             the sequence place, then dest, then the removal
{"truncate"}        the sequence place, then the length
{"reserve"}         the sequence place, then the capacity
{"if"} {"while"}    the condition
{"switch"}          the value
{"return"}          the value
{"call"}            the arguments left to right, in the parameter order, each
                    fully resolved before the next; then the call; then the
                    store into dest
```

Resolving a place means evaluating its index expressions and performing their
bounds checks, in the left-to-right order in which they appear. So
`v[i] = w[j]` checks `i` against `len(v)` before evaluating `w[j]`, and a call
whose second argument traps has already resolved the first.

The one rule that is not simply "left to right" is that a destination place is
resolved before the value being stored into it. Written the other way round,
`v[bad] = w[alsobad]` would report the right-hand side's trap, so which trap a
program reports would depend on how much work its right-hand side happens to
do before failing. Section 16 notes that Go's own order is the opposite one,
which is why the printer has to emit the check rather than lean on the
language.

## 14. Canonical JSON serialization

The artifact is one JSON file, `engine.tir.json`. Its SHA-256 is the identity
that ties the Lean proofs, the backends and CI together (DESIGN.md section
3.3), so the encoding has to be a function of the program and nothing else —
no map iteration order, no locale, no timestamps, no floats.

The Lean decoder re-serializes what it decoded and byte-compares it against
the input as a self-check, so these rules are as normative as the semantics.
An artifact this project ships is therefore always canonical: the generator
writes nothing else, and CI fails on a file that is not.

```
encoding        UTF-8 with no BOM; the output is pure ASCII
line endings    LF; the file ends with exactly one LF
indentation     two spaces per nesting level
objects         keys sorted ascending by Unicode code point; one member per
                line as "key": value; a comma ends every line but the last;
                an empty object is {} on one line
arrays          one element per line, same comma rule; an empty array is []
numbers         integers only: an optional -, then digits with no leading
                zero (except 0 itself), no +, no exponent, no fraction
strings         " delimited; \" and \\ for those two characters; \b \t \n \f
                \r for those five controls; \u00xx with lowercase hex for
                every other character below 0x20; every character from 0x20
                to 0x7e literally, except the two escaped above; every
                character above 0x7e as \uxxxx with lowercase hex, using a
                surrogate pair above the BMP
booleans        true, false
null            null
```

Byte payloads — constant `bytes` values — are lowercase hex strings of even
length. Nothing else in the artifact carries binary.

Declaration lists are sorted by name: `enums`, `structs`, `consts` and `funcs`
each ascend by the `name` member. Everything that is a declaration rather than
a set is left in the author's order: enum variant lists, struct field lists,
parameter lists, argument lists, statement bodies, and switch arms.

A parser may accept any whitespace — that part is not its business — but it
must reject anything the canonical form could not have *meant*: duplicate
object keys, floats, the `NaN` and `Infinity` literals some JSON parsers
allow, a member no reader consumes, and a name that is not an identifier.
Whether a file is canonical byte for byte is a separate question, and the way
to ask it is to decode it and re-encode the result: that comparison is exactly
the Lean round-trip self-check, and `is_canonical` is the Python side of it.

## 15. Validator rules

The validator is what stands between the untrusted authoring DSL and everything
downstream. Each rule below has a number, a statement, and at least one
negative test that trips it, in `tests/test_tir_validate.py` — except V-001,
which the reader enforces, because a decoded program no longer carries a
version to check, and whose test lives in `tests/test_tir_serialize.py`.

That last sentence is checked rather than asserted: the test session records
every rule it manages to provoke and fails over one nobody did. Looking for a
rule's number in a test file would prove only that somebody typed it.

**Program structure**

```
V-001  tir is exactly the integer 1
V-002  top-level names — enums, enum variants, structs, consts, funcs — are
       pairwise distinct
V-003  every enum, struct, constant, function and enum variant a program
       names is declared
V-004  an enum declares at least one variant, with distinct names
V-005  a struct declares at least one field, with distinct names, and struct
       definitions are not recursive
```

**Types**

```
V-006  a vec element type is copyable
V-007  a vec maximum N is an integer, and 1 <= N <= floor(CEILING /
       sizeof(elem))
V-008  frozen applies only to a linear type
V-009  frozen does not nest
V-010  the full-width u8 sequence is spelled "bytes", never
       {"vec": {"elem": "u8", "max": 2147483647}}
```

**Constants**

```
V-011  a constant's type is a scalar, an enum, or a frozen type
V-012  a constant's value matches its type: integers in range, struct fields
       exactly once, vec length at most the maximum, bytes payloads
       even-length lowercase hex and a string of bytes once decoded. Whether
       a named variant exists is V-003
```

**Expressions**

```
V-013  every expression is well typed: the operator is one section 6 lists,
       operand types match it and each other, index expressions are u32,
       conditions are bool, and a call's arguments match the signature in
       count, mode and type
V-014  a literal's value really is an integer, or a bool for "bool", and is in
       the range of its named type
V-015  a shift count is an integer in 0 .. w-1 for the operand's width
V-016  shr takes u8 or u32, sar takes i32, shl takes u8, i32 or u32
V-017  a struct literal names every field exactly once and its struct type is
       copyable
```

**Functions and calls**

```
V-018  an in parameter's type is copyable
V-019  a return type is copyable
V-020  a call has a dest exactly when the callee returns a value, and the
       dest's type is the return type
V-021  the call graph is acyclic, self-calls included
V-022  at a call site, every inout argument's access path is provably
       disjoint from every other argument's paths and from dest
```

**Statements**

```
V-023  a linear-typed expression appears only as the base of a field, index,
       len or cap, or as the src of a copy; used as a value anywhere else it
       is rejected
V-024  assign requires a copyable type on both sides, of equal type
V-025  an in parameter is not written
V-026  no write passes through a frozen prefix, and no sequence statement
       takes a frozen sequence
V-027  no statement follows a return, break or continue in the same body
V-028  take: same type, both writable, provably disjoint
V-029  swap: same type, both writable, provably disjoint
V-030  copy: src of T or frozen<T>, dest of T, provably disjoint
V-031  push and pop: the sequence place and the value or dest place are
       provably disjoint
V-032  switch arms belong to the enum, do not repeat, and either cover it
       with default null or leave a gap with a default body
V-033  break and continue appear inside a while body
V-034  return carries a value exactly when the function declares a return
       type, of that type
V-035  every path through a value-returning function ends in a return
V-036  a while variant has type counter
V-037  a let has an initializer only for a copyable type, of that type
V-038  names do not shadow: parameters and locals are distinct from each
       other and from every top-level name
V-039  every variable an expression or a place mentions is a parameter or a
       local in scope. That a projection exists — a field of that struct, an
       index into a sequence — is typing, hence V-013
V-040  a parameter's mode is 'in' or 'inout'
V-041  every name a program declares — enum, variant, struct, field,
       constant, function, parameter, local — is an identifier of at most
       64 characters
V-042  every node is a form this document defines: a statement where a
       statement belongs, an expression where an expression belongs, a place
       where a place belongs, a type from section 3.1, a declaration of the
       kind its list is for, and a list wherever a list belongs — a body, an
       enum's variants, a struct's fields, a switch's arms, a call's
       arguments. Whether a payload fits is the rule that governs that
       payload: V-014, V-015, V-007, V-012
V-043  no declared name is a reserved word of section 2, and none begins
       with either of the printers' prefixes, 'tir_' and 'Tir_'
V-044  nothing nests more than 64 deep, counted as section 2 counts it:
       statements and the expressions and places inside them, a constant's
       value, a chain of struct containment, a path through the call graph
```

Rule numbers are stable. A rule that is dropped leaves its number retired
rather than reused, so a test name never comes to mean something else.

## 16. Backend lowering requirements

These are obligations on the printers, stated here because they are how the
semantics above survives the trip to a host language. The printers themselves
arrive in M4; this section is what they will be built and reviewed against,
and nothing in it is a claim about code that exists today.

**Go**

- `counter` is `uint64` with the section 6.7 helpers; the pre-check forms are
  used verbatim, not replaced by an add-then-clamp.
- `i32`/`u32`/`u8` arithmetic is native Go arithmetic on `int32`/`uint32`/
  `byte`, which already wraps.
- `div` and `rem` go through helpers, because Go panics on a zero divisor and
  on `math.MinInt32 / -1`, and both are defined results here.
- Sequences are slices manipulated only through generated push/reserve/
  truncate helpers that check the declared maximum *before* allocating. A raw
  `append` reallocates first and checks afterwards, which would report the
  wrong peak.
- Checked indexing is ordinary Go indexing: the native bounds-check panic is
  the trap, documented as the engine-bug channel.
- An assignment to an element must have its bounds check emitted *before* the
  right-hand side is evaluated. Go's own order is the other way round — for
  `a[i] = e` it evaluates `e` and checks the index at the assignment — and
  section 13 pins the destination first. Both sides are pure, so the only
  difference is which trap fires when two could, but that is an observable
  and it has to match.
- `inout` is a pointer.
- A copyable struct is a value, and Go copies one on assignment, which is
  what section 4's reading of storage means. Nothing extra is needed here;
  the note exists because JavaScript needs the opposite.
- A frozen value is an ordinary Go value shared by reference and never
  written; the printer emits no mutating path for one.

**JavaScript**

- `counter` is a plain number with the same pre-checked helpers.
- 32-bit arithmetic is coerced with `| 0` and `>>> 0`, except multiplication,
  which must use `Math.imul` — a plain double product loses low bits above
  2^53 before any coercion runs. This is the one place where naive lowering is
  silently wrong rather than merely slow, and the conformance suite aims at it
  directly.
- `u8` arithmetic is masked with `& 255`, `shl` on `u8` included.
- `shr` is `>>>` and `sar` is `>>`. The two spellings of section 6.10 exist so
  that this mapping is a lookup rather than a judgement.
- Checked indexing emits an explicit bounds test that throws. An out-of-range
  typed-array read yields `undefined` instead of failing, so the trap has to
  be written out. Since the check is emitted rather than native, it goes
  before the right-hand side of an assignment, as section 13 requires.
- **A copyable struct value must be cloned when it is read out of storage.**
  A class instance is a reference in JavaScript, so `let q = p` would alias
  where Go copies, and a later write through `q` would be visible through `p`.
  Every read of a struct-typed variable, field or element emits a
  field-by-field clone; frozen values inside it are shared, not cloned. This
  is the JavaScript counterpart of the `Math.imul` trap: naive lowering is
  silently wrong rather than slow, so the conformance suite aims at it.
- Every sequence is a backing store plus an explicit length field. Which
  backing store is fixed per element type, not left to the printer:

```
+------------------+------------------+-------------------------------------+
| element type     | JavaScript       | Go                                  |
+------------------+------------------+-------------------------------------+
| u8 (and bytes)   | Uint8Array       | []byte                              |
| i32              | Int32Array       | []int32                             |
| u32              | Uint32Array      | []uint32                            |
| counter          | Float64Array     | []uint64                            |
| an enum          | Int32Array       | []E, E being the typed int constant |
| bool             | Array            | []bool                              |
| frozen<T>        | Array            | []T                                 |
| a struct         | Array of class   | []S                                 |
|                  | instances        |                                     |
+------------------+------------------+-------------------------------------+
```

  `counter` fits a `Float64Array` exactly because every counter value is at
  most 2^53 - 1. A struct element is a class instance whose constructor
  initializes every field, which is what keeps the shape monomorphic for the
  JITs.
- Growth allocates a new buffer and copies, on the same schedule as Go.
- `inout` of a scalar is a one-field cell; `inout` of an object passes the
  object.

**Both**

- **The generated scope holds nothing but the program.** A printer emits TIR
  names verbatim (section 2), and that is only safe if the scope those names
  land in contains just them and the `tir_` helpers. So the printer owns a
  package of its own — a Go package, an ES module — and the hand-written
  wrapper is a *different* one that imports it. Otherwise the wrapper's own
  `Compile`, `Regexp` or `Generated` would sit in the same scope as the
  program's names, and V-043 would have to grow a list of names that live
  outside TIR and change without notice. What the generated scope *does* hold
  besides the program — the `tir_` helpers, the `Tir_` façade, the hash
  constant, and the host globals the module reads — is in V-043 precisely
  because it is printer-owned and moves only when this document does.
- A printer may recurse over the program without a depth guard of its own, and
  emit nesting verbatim without one either. Rule V-044 is what buys that, and
  it is the reason the rule exists rather than a happy consequence of it.
- Iteration is always index-based. There is no iteration order to disagree
  about because there is no iteration construct: `while` and explicit indices
  are all TIR has.
- The declared loop variant is not printed.
- The artifact's SHA-256 appears in a header comment and in a constant, and CI
  refuses to ship files whose hashes disagree.
