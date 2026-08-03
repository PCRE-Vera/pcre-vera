"""The toy TIR program the golden tests round-trip.

Bounded Fibonacci with an explicit stack, which is the shape DESIGN.md section
9 asks M2 to demonstrate and, not by accident, the shape the real engine's
matchers have: no recursion, a vec of frames, a tag saying where each frame
left off, and a fuel bound the loop variant is read from.

It also carries a frozen byte constant and a function that reads it, because a
generated table read through a shared immutable value is the other thing the
engine does constantly.
"""

from __future__ import annotations

from pathlib import Path

from pcrevera.dsl import (
    Module,
    boolean,
    bytes_,
    counter,
    frozen,
    inout,
    land,
    u8,
    u32,
    vec,
)
from pcrevera.tir import ir

STACK_MAX = 64
FUEL = 10_000

BITS = bytes([1, 2, 4, 8, 16, 32, 64, 128])

GOLDEN = Path(__file__).parent / "golden" / "toy.tir.json"


def build() -> ir.Program:
    m = Module()

    Phase = m.enum("Phase", ["Enter", "AfterFirst", "AfterSecond"])
    Task = m.struct("Task", [("n", u32), ("phase", Phase), ("saved", counter)])
    Stack = vec(Task, STACK_MAX)
    bits = m.const("BITS", frozen(bytes_), BITS)

    push_task = m.func("push_task", params=[("stack", Stack, "inout"), ("k", u32)])
    push_task.push(
        push_task["stack"],
        Task.of(n=push_task["k"], phase=Phase.Enter, saved=counter(0)),
    )

    # masked(i) is the table-lookup idiom TIR-SPEC.md section 6.10 points at:
    # a variable shift written as an index into a constant.
    masked = m.func("masked", params=[("i", u8)], ret=u8)
    masked.ret(bits.at(masked["i"].cast(u32) & u32(7)))

    fib = m.func("fib", params=[("n", u32), ("out", counter, "inout")], ret=boolean)
    stack = fib.let("stack", Stack)
    fuel = fib.let("fuel", counter, counter(FUEL))
    result = fib.let("result", counter, counter(0))
    done = fib.let("done", Task)
    fib.call("push_task", [inout(stack), fib["n"]])

    with fib.while_(land(stack.len() > u32(0), fuel > counter(0)), fuel):
        fib.set(fuel, fuel - counter(1))
        top = fib.let("top", u32, stack.len() - u32(1))
        with fib.switch(stack.at(top).field("phase")) as phase:
            with phase.case("Enter"):
                # The frame's own n has to come out into a local first: a push
                # may move the buffer, so V-031 refuses to read the sequence
                # while pushing onto it.
                k = fib.let("k", u32, stack.at(top).field("n"))
                with fib.if_(k <= u32(1)):
                    fib.set(result, k.cast(counter))
                    fib.pop(stack, done)
                with fib.else_():
                    fib.set(stack.at(top).field("phase"), Phase.AfterFirst)
                    fib.call("push_task", [inout(stack), k - u32(1)])

            with phase.case("AfterFirst"):
                fib.set(stack.at(top).field("saved"), result)
                fib.set(stack.at(top).field("phase"), Phase.AfterSecond)
                second = fib.let("second", u32, stack.at(top).field("n"))
                fib.call("push_task", [inout(stack), second - u32(2)])

            with phase.case("AfterSecond"):
                fib.set(result, stack.at(top).field("saved") + result)
                fib.pop(stack, done)

    fib.set(fib["out"], result)
    # An exhausted fuel budget leaves frames on the stack, and that is exactly
    # what the answer reports.
    fib.ret(stack.len() == u32(0))

    return m.build()


def fibonacci(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


if __name__ == "__main__":
    # `python tests/toy.py` rewrites the golden artifact. Changing it is a
    # deliberate act, so it is a command rather than something a test run does
    # quietly on its way past.
    from pcrevera.tir import dumps, validate

    program = build()
    validate(program)
    GOLDEN.write_text(dumps(program))
    print(f"wrote {GOLDEN}")
