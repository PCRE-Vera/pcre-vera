"""The theorem inventory, held to the Lean it names.

The inventory exists because `THEOREMS.md` cannot be checked. It is prose, and
prose that names a theorem is right until somebody renames the theorem — which
had already happened once when this file was written, the Pike refinement
having been recorded under a name Lean does not have.

So every declaration here is resolved against the sources rather than
transcribed, and this holds the resolution to the files: the module exists, it
declares that name exactly once, and the hash beside it is the hash of the
bytes on disk. What the capsule verifier adds on top is elaboration — that the
name is not merely written somewhere but is a declaration Lean accepts, with
no axiom beyond the three.
"""

from __future__ import annotations

import hashlib
import json
import re

import pytest

from pcrevera.capsule import inventory, leancheck
from pcrevera.paths import REPO_ROOT
from pcrevera.tir import serialize

ARTIFACT = REPO_ROOT / "gen" / "engine.tir.json"
LEDGER = REPO_ROOT / "conformance" / "layer-i.json"

PROGRAM = serialize.loads(ARTIFACT.read_text())
SHA256 = hashlib.sha256(ARTIFACT.read_bytes()).hexdigest()
BUILT = json.loads(inventory.PATH.read_text())


def test_the_inventory_is_what_the_sources_say() -> None:
    assert inventory.PATH.read_text() == inventory.render(
        inventory.build(PROGRAM, SHA256)
    )


def test_the_inventory_names_the_artifact_it_was_computed_from() -> None:
    assert BUILT["artifact"] == SHA256


def test_every_claim_has_an_identifier_of_its_own() -> None:
    ids = [claim["id"] for claim in BUILT["claims"]]
    assert len(set(ids)) == len(ids)


@pytest.mark.parametrize("claim", BUILT["claims"], ids=lambda c: c["id"])
def test_the_vocabulary_is_the_declared_one(claim: dict) -> None:
    assert claim["kind"] in inventory.KINDS
    assert claim["status"] in inventory.STATUSES
    assert claim["layer"] in ("S", "R", "L", "I")
    assert claim["statement"] and claim["domain"]


@pytest.mark.parametrize("claim", BUILT["claims"], ids=lambda c: c["id"])
def test_a_claim_names_lean_exactly_where_it_has_some(claim: dict) -> None:
    """An absent claim names nothing, and everything else names something.

    The point of recording the gaps is that they stay gaps: a row that quietly
    acquired a declaration would be a status change nobody reviewed.
    """
    if claim["status"] == "absent":
        assert claim["declarations"] == []
    else:
        assert claim["declarations"]


@pytest.mark.parametrize("claim", BUILT["claims"], ids=lambda c: c["id"])
def test_every_declaration_is_a_file_with_that_hash(claim: dict) -> None:
    for decl in claim["declarations"]:
        path = REPO_ROOT / decl["module"]
        assert path.is_file(), decl["module"]
        assert decl["sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()


@pytest.mark.parametrize("claim", BUILT["claims"], ids=lambda c: c["id"])
def test_every_named_declaration_is_declared_once_in_its_module(claim: dict) -> None:
    for decl in claim["declarations"]:
        if "lean" not in decl:
            continue
        source = (REPO_ROOT / decl["module"]).read_text()
        assert decl["lean"] in inventory.declarations(source).values()


def test_the_layer_i_domain_is_the_artifacts_own() -> None:
    """The one part of the inventory nobody writes.

    A helper added to the engine appears here without a theorem, and the count
    moves with it, which is what keeps the layer I row from being a sentence
    somebody last checked in June.
    """
    ledger = json.loads(LEDGER.read_text())
    assert BUILT["layerI"]["domain"] == [e["name"] for e in ledger["post_parse"]]
    assert BUILT["layerI"]["functions"] == ledger["post_parse"]
    assert BUILT["layerI"]["counts"]["owed"] == ledger["counts"]["post_parse"]
    assert BUILT["layerI"]["counts"]["proved"] == ledger["counts"]["proved"]


def test_the_prose_inventory_still_carries_every_row() -> None:
    """`THEOREMS.md` and this file have to talk about the same claims.

    Not the same theorem names — that is the drift the inventory replaces — but
    the same identifiers, so a row cannot be dropped from one side alone.
    """
    text = (REPO_ROOT / "THEOREMS.md").read_text()
    missing = [
        claim["id"]
        for claim in BUILT["claims"]
        if not re.search(rf"(?<![\w-]){re.escape(claim['id'])}(?![\w-])", text)
    ]
    assert missing == []


def table_cells() -> dict[str, str]:
    """The third column of `THEOREMS.md`'s three-column tables, per row id.

    A hash does not fit in a table cell and neither does a list of modules, so
    a row runs over several lines with the id blank after the first; joining
    them is what makes the cell one string again.
    """
    cells: dict[str, str] = {}
    current = ""
    for line in (REPO_ROOT / "THEOREMS.md").read_text().splitlines():
        stripped = line.strip()
        if not stripped.startswith("|") or not stripped.endswith("|"):
            continue
        parts = [cell.strip() for cell in stripped.strip("|").split("|")]
        if len(parts) != 3:
            continue
        if parts[0]:
            current = parts[0]
        if current:
            cells[current] = cells.get(current, "") + " " + parts[2]
    return cells


def test_every_module_the_prose_row_names_is_one_the_claim_records() -> None:
    """The direction that caught a real omission.

    `THEOREMS.md`'s S-8 row names `Proofs/PikeRefine.lean`, and a first draft of
    the inventory recorded only the `ExecPike.lean` wrapper above it — so the
    source hash pinned for the Pike half was the hash of a file that does not
    contain the proof. Prose is not the authority here, but a module it names
    and the inventory does not is a gap in the inventory.
    """
    recorded = {
        claim["id"]: {decl["module"] for decl in claim["declarations"]}
        for claim in BUILT["claims"]
    }
    gaps = {}
    for row, blob in table_cells().items():
        if row not in recorded:
            continue
        named = set(re.findall(r"((?:Spec|Ref|Proofs|Tir|Corpus)/[A-Za-z]+\.lean)", blob))
        held = {module.split("Pcrevera/")[-1] for module in recorded[row]}
        if named - held:
            gaps[row] = sorted(named - held)
    assert gaps == {}


def test_a_missing_theorem_is_a_failure_rather_than_a_blank(tmp_path) -> None:
    """The check the inventory exists for, run against a source it will not
    find the name in."""
    module = tmp_path / "Mod.lean"
    module.write_text("namespace N\ntheorem other : True := trivial\nend N\n")
    claim = inventory.Claim(
        "X-1", "S", "proof", "complete", "a claim", "a domain",
        (inventory.Decl("Mod.lean", "wanted"),),
    )
    with pytest.raises(LookupError, match="wanted"):
        inventory.resolve(claim, claim.decls[0], tmp_path)


def test_two_declarations_of_one_name_resolve_to_neither() -> None:
    """A short name that means two things is not a name the inventory can use,
    and guessing the first would pin the wrong theorem."""
    source = "namespace A\ndef x := 1\nend A\nnamespace B\ndef x := 2\nend B\n"
    assert "x" not in inventory.declarations(source)


def test_root_escapes_the_namespace_it_sits_in() -> None:
    source = "namespace A\ndef _root_.B.y := 1\nend A\n"
    assert inventory.declarations(source)["y"] == "B.y"


def test_prose_that_starts_a_line_with_a_keyword_is_not_a_scope() -> None:
    """`Basic.lean` opens with a doc comment whose second sentence starts a
    line with the word `namespace`. Reading that as one puts every declaration
    in the file a level too deep, and the wrong name still looks like a name."""
    source = "/-!\nnamespace under `Pcrevera`:\n-/\ndef y := 1\n"
    assert inventory.declarations(source) == {"y": "y"}


def test_a_dash_inside_a_string_is_not_a_comment() -> None:
    source = 'def sep : String := "--"\ndef y := 1\n'
    assert set(inventory.declarations(source)) == {"sep", "y"}


def test_mutual_and_section_do_not_reach_the_qualified_name() -> None:
    source = (
        "namespace A\nsection\nmutual\ndef x := 1\nend\nend\n"
        "section Named\ndef y := 2\nend Named\nend A\n"
    )
    assert inventory.declarations(source) == {"x": "A.x", "y": "A.y"}


def test_a_namespace_may_be_closed_one_component_at_a_time() -> None:
    """Legal Lean, and the shape that made a first attempt at this reader lose
    track of where it was."""
    source = "namespace A.B\ndef x := 1\nend B\ndef y := 2\nend A\n"
    assert inventory.declarations(source) == {"x": "A.B.x", "y": "A.y"}


def test_an_end_that_closes_nothing_is_refused_rather_than_ignored() -> None:
    with pytest.raises(inventory.ScopeError, match="closes nothing open"):
        inventory.declarations("namespace A\ndef x := 1\nend B\n")


def test_a_raw_string_toggles_nothing_on_its_way_past() -> None:
    """`r#"..."#` ends at a quote followed by as many hashes as opened it, so
    the quotes inside one are content. A reader that treated them as
    delimiters would step out of the string mid-way and read `namespace` in
    its text as a scope."""
    source = 'namespace A\ndef s := r#"\n"\nnamespace Bogus\n"\n"#\ndef y := 1\n'
    assert inventory.declarations(source)["y"] == "A.y"


def test_a_quote_character_literal_is_not_a_string() -> None:
    """`Print.lean` writes `if c = '"' then`, which is the one place in the
    tree where missing this would matter."""
    source = "def q := if c = '\"' then 1 else 2\nnamespace A\ndef y := 1\nend A\n"
    assert inventory.declarations(source) == {"q": "q", "y": "A.y"}


def test_an_apostrophe_in_a_name_survives_the_axiom_report() -> None:
    """Lean lets an identifier end in `'`, and then prints `'foo'' depends…`."""
    report = inventory.axioms_used(
        "'foo'' does not depend on any axioms\n"
        "'bar' depends on axioms: [propext, Quot.sound]\n"
    )
    assert report == {"foo'": [], "bar": ["propext", "Quot.sound"]}


def test_the_whole_lean_tree_reads_without_losing_its_place() -> None:
    """The resolver is only worth something if it never guesses, so it is run
    over every module rather than over the ones the inventory happens to name."""
    for path in sorted((REPO_ROOT / "lean").rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        inventory.declarations(path.read_text())


@pytest.mark.skipif(not leancheck.built(), reason="the Lean package is not built")
def test_lean_refuses_a_name_it_does_not_have() -> None:
    """The other half of the elaboration check: that it can fail.

    A check nobody has watched fail is a check nobody has watched.
    """
    invented = json.loads(json.dumps(BUILT))
    invented["claims"] = [
        {
            "id": "X-1",
            "layer": "S",
            "kind": "proof",
            "status": "complete",
            "statement": "a theorem nobody wrote",
            "domain": "nothing",
            "features": [],
            "declarations": [
                {
                    "module": "lean/Pcrevera/Spec/Ast.lean",
                    "sha256": "0" * 64,
                    "lean": "Pcrevera.no_such_theorem",
                }
            ],
        }
    ]
    with pytest.raises(leancheck.CheckError):
        leancheck.run(invented)


@pytest.mark.skipif(not leancheck.built(), reason="the Lean package is not built")
def test_lean_itself_confirms_every_name_the_inventory_records() -> None:
    """The check the rest of this file cannot make.

    Everything above reads the sources with the same reader that wrote the
    inventory, so a reader that is wrong stays undetected. This asks Lean:
    every recorded name elaborates, and every one of them rests on the three
    axioms and nothing else. `make lean` runs it too, so a checkout without a
    build is the only place it is skipped.
    """
    reported = leancheck.run(BUILT)
    recorded = {
        decl["lean"]
        for claim in BUILT["claims"]
        for decl in claim["declarations"]
        if "lean" in decl
    }
    assert recorded <= set(reported)
    for name, used in reported.items():
        assert set(used) <= set(inventory.AXIOMS), name
