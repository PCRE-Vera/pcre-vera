"""Syntax-directed printers from TIR to source text, and the files they write.

`generate` is the whole pipeline in one function: build the engine, serialize
it canonically, hash that text, and print both backends against that hash.
Every output is a function of its inputs and nothing else: the program for the
artifact and the two backends; the program and the pattern populations for the
conformance files and the migration report; the two corpora this run has just
generated for the Lean bridge. So building and verifying are the same
computation asked either to write the files or to compare them, and neither
reads a generated file back.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from .. import leanexport
from ..leanexport import bridge
from ..engine import certificate_corpus, migration
from ..engine.program import program
from ..oracle import conformance
from ..paths import GEN_DIR
from ..sweep import shard
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
        Output(certificate_corpus.PATH, certificate_corpus.corpus_text()),
        Output(shard.PATH, shard.corpus_text()),
        Output(migration.PATH, migration.corpus_text()),
        # The AST bridge is a function of the two corpora it feeds the Lean
        # replay of, computed from the same fresh texts so that verifying it
        # never depends on what happens to be on disk.
        Output(
            bridge.BRIDGE_PATH,
            bridge.text(
                json.loads(conformance.corpus_text()),
                json.loads(shard.corpus_text()),
            ),
        ),
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
