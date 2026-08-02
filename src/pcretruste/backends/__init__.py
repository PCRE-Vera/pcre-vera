"""Syntax-directed printers from TIR to source text, and the files they write.

`generate` is the whole pipeline in one function: build the engine, serialize
it canonically, hash that text, and print both backends against that hash.
Every output is a function of the program alone, so building and verifying are
the same computation asked either to write the files or to compare them.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .. import leanexport
from ..engine.program import program
from ..oracle import conformance
from ..paths import GEN_DIR
from . import go, js, lowering

GO_PATH = GEN_DIR / "go" / "internal" / "engine" / "engine.go"
JS_PATH = GEN_DIR / "js" / "engine.mjs"
PROBE_GO_PATH = GEN_DIR / "go" / "internal" / "probe" / "probe.go"
PROBE_JS_PATH = GEN_DIR / "js" / "probe.mjs"

PROBE_SUMMARY = (
    "The lowering probe: a small TIR program that does on purpose what the "
    "printers can get wrong, with operands sitting on the boundaries. It is test "
    "material, not part of the library; conformance/lowering.json says what every "
    "call has to answer."
)


@dataclass(frozen=True)
class Output:
    path: Path
    text: str

    def matches(self) -> bool:
        return self.path.exists() and self.path.read_text(encoding="utf-8") == self.text

    def write(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(self.text, encoding="utf-8")


def generate() -> tuple[str, list[Output]]:
    """The artifact hash, and every file the generator owns."""
    built = program()
    artifact = leanexport.artifact(built)
    sha256 = leanexport.digest(artifact)

    probe = lowering.program()
    probe_artifact = leanexport.artifact(probe)
    probe_sha = leanexport.digest(probe_artifact)

    return sha256, [
        Output(leanexport.ARTIFACT_PATH, artifact),
        Output(GO_PATH, go.render(built, sha256)),
        Output(JS_PATH, js.render(built, sha256)),
        Output(
            PROBE_GO_PATH,
            go.render(
                probe,
                probe_sha,
                package="probe",
                origin="the lowering probe",
                summary=PROBE_SUMMARY,
            ),
        ),
        Output(
            PROBE_JS_PATH,
            js.render(probe, probe_sha, origin="the lowering probe", summary=PROBE_SUMMARY),
        ),
        Output(conformance.PATH, conformance.corpus_text()),
        Output(lowering.PATH, lowering.corpus_text()),
    ]


__all__ = [
    "GO_PATH",
    "JS_PATH",
    "PROBE_GO_PATH",
    "PROBE_JS_PATH",
    "Output",
    "generate",
    "go",
    "js",
    "lowering",
]
