# pcre-truste

An experiment to see if AI can build PCRE-compatible regex engines that aren't garbage.

A generator for a PCRE engine whose cost you can know in advance: one engine,
written once in a small verified-friendly IR, proved in Lean against a
mechanized PCRE specification, and printed out as idiomatic Go and JavaScript.
A compiled pattern can tell you its worst-case cost, stack, and memory before
you ever run it, and every match runs under hard limits.

What that buys, said the way DESIGN.md section 5 insists on saying it:
deterministically bounded work per call, every instruction charged and every
scratch byte accounted, and allocation-free matching when a preallocated
context is used. It does not turn Go or a browser into a hard-realtime system.
Garbage collection, JIT warmup, and scheduling belong to the host runtime and
sit outside the model.

`objective.md` says what this is for. `DESIGN.md` says how it gets built, in
detail, from the IR design through the proof layering to the milestones.

## Where the project is

M0 (scaffolding) and M1 (the pcre2 oracle) are done. There is no engine yet:
the parser, the bytecode compiler, and the matchers arrive in M3, the Go and
JavaScript backends in M4, and the Lean proofs from M6 on.

What works today is the thing everything else leans on — the reference. pcre2
is not one behavior, it is one build, so `oracle/pcre2-pin.toml` pins the
release, its tarball hash, the complete configure flags, and every field the
linked library must report back about itself, down to the 1088 bytes of default
character tables that decide what `\w` and `\b` mean. The one knob that
`pcre2_config` cannot report is pinned by behavior in the corpus instead.
`make oracle-verify` builds that exact library from source and checks it, and
`oracle/pcre2shim/shim.c` answers questions about it over a line protocol so
the rest of the project can ask pcre2 what a pattern does.

## Getting started

```
make setup          # the Python environment, through uv
make oracle-verify  # build the pinned pcre2 and check it against the pin
make test           # the Python tests, seed corpus included
make check          # all of the above, plus lake build, go test, node --test
```

The oracle build downloads a 2 MB tarball and compiles the 8-bit library only,
which takes a few seconds. `oracle/README.md` covers the protocol, the pin, and
the environment variables for a build machine with a shared cache or no
network.

## Layout

```
+-------------------+------------------------------------------------------+
| objective.md      | what the project is for                              |
| DESIGN.md         | the plan, in full                                    |
| LOG.md            | what was asked and what was done, step by step       |
| MISTAKES.md       | what earlier drafts got wrong, kept as a trap list   |
| api-faq.md        | APIs that did not behave the way we first assumed    |
| src/pcretruste/   | the generator and all its tooling                    |
| oracle/           | the pcre2 pin, the C shim, the seed corpus           |
| lean/             | the lake project: the four proof layers              |
| gen/go, gen/js    | generated code plus hand-written wrappers            |
| conformance/      | the language-neutral corpus (arrives with M4)        |
| tmp/              | scratch, never committed                             |
+-------------------+------------------------------------------------------+
```

## What is and is not claimed

Worth saying early, because the point of the exercise is precision. The
theorems, once they exist, will cover the IR artifact under the TIR semantics.
The translation from that artifact to Go and JavaScript is a separate link,
kept small and covered by cross-implementation testing, and the generated
libraries are never described as formally verified — they are generated from a
formally verified artifact by a printer that is tested. Equally, no theorem can
relate our specification to the pinned C library; that correspondence rests on
the specification being readable and on differential testing, feature by
feature. DESIGN.md sections 3.3 and 6 spell both out.
