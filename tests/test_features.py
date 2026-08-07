"""The feature ledger, and the rule that stops it from being a wish list.

A ledger where `default` is a field somebody sets would be worth nothing: the
whole point of gating is that admission follows the proof status rather than
the other way round. So the flag is recomputed from the four status columns and
compared, and the one exception — wave 1's documented M7 foundation fallback —
has to be spelled out in the row rather than inferred from the wave number.

The mutations below are the failures that matter. Each one is a plausible edit
somebody would make to ship a feature early, and each one has to be refused by
name.
"""

from __future__ import annotations

import copy
import json

import pytest

from pcrevera.capsule import canonical, features, inventory
from pcrevera.paths import REPO_ROOT
from pcrevera.tir import serialize

ARTIFACT = REPO_ROOT / "gen" / "engine.tir.json"
PROGRAM = serialize.loads(ARTIFACT.read_text())

LEDGER = features.load()
INVENTORY = json.loads(inventory.PATH.read_text())


def mutate(change) -> features.LedgerError:
    """Apply one edit to a copy of the ledger and return the refusal it earns."""
    broken = copy.deepcopy(LEDGER)
    change(broken)
    with pytest.raises(features.LedgerError) as raised:
        features.validate(broken)
    return raised.value


def row(ledger: dict, key: str) -> dict:
    return next(r for r in ledger["features"] if r["key"] == key)


def test_the_committed_ledger_is_canonical_and_valid() -> None:
    assert canonical(LEDGER) == features.PATH.read_text()


def test_the_three_sets_partition_the_ledger() -> None:
    sets = features.sets(LEDGER)
    keys = {r["key"] for r in LEDGER["features"]}
    joined = sets["default"] + sets["gated"] + sets["unsupported"]
    assert len(joined) == len(keys)
    assert set(joined) == keys


def test_no_wave_two_family_is_in_the_default_surface() -> None:
    """M8's standing condition, checked rather than promised."""
    assert [r["key"] for r in LEDGER["features"] if r["wave"] != 1 and r["default"]] == []


def test_the_fallback_basis_is_wave_ones_alone() -> None:
    for r in LEDGER["features"]:
        if r["admissionBasis"] == features.FALLBACK:
            assert r["wave"] == 1


def test_every_claim_a_row_spends_is_a_complete_one() -> None:
    """A row cannot lean on a theorem the inventory says is missing."""
    features.check_against_inventory(LEDGER, INVENTORY)


def test_an_implemented_row_has_to_name_a_proof() -> None:
    """Otherwise the join above is vacuous: a row with no claims satisfies
    "every named proof is in the capsule" by naming none."""
    assert "names no proof" in str(
        mutate(lambda ledger: row(ledger, "syntax.dot").update(claims=[]))
    )


def test_a_claim_that_does_not_cover_the_feature_is_a_refusal() -> None:
    """The bypass the join exists to close.

    S-1 is complete, is in the capsule, and says nothing whatever about atomic
    groups. A row that spent it would have satisfied every earlier version of
    this check while proving nothing about itself.
    """
    broken = copy.deepcopy(LEDGER)
    entry = row(broken, "syntax.atomic")
    entry.update(
        implementation="complete",
        artifactVersion=2,
        s="complete",
        r="complete",
        i="complete",
        claims=["S-1"],
        admissionBasis="proof-chain",
        default=True,
        gated=True,
    )
    features.validate(broken)
    with pytest.raises(features.LedgerError, match="does not cover"):
        features.check_against_inventory(broken, INVENTORY)


def test_a_column_complete_on_definitions_alone_is_a_refusal() -> None:
    """S-1, S-2 and S-4 are spellings in Lean, not proofs of anything. A row
    whose S column says complete has to have a proof of layer S behind it."""
    broken = copy.deepcopy(LEDGER)
    row(broken, "syntax.dot")["claims"] = ["S-1", "S-2", "S-4", "R-6"]
    with pytest.raises(features.LedgerError, match="layer S"):
        features.check_against_inventory(broken, INVENTORY)


def test_the_wave_one_feature_list_is_the_ledgers_own() -> None:
    """`inventory.WAVE1_FEATURES` decides which rows an S or R claim covers, so
    a wave 1 row added to the ledger and not to it would silently lose its
    proofs."""
    assert set(inventory.WAVE1_FEATURES) == {
        r["key"] for r in LEDGER["features"] if r["wave"] == 1
    }


def test_a_claim_the_capsule_does_not_carry_is_a_refusal() -> None:
    broken = copy.deepcopy(LEDGER)
    row(broken, "syntax.dot")["claims"] = ["I-10"]
    with pytest.raises(features.LedgerError, match="I-10"):
        features.check_against_inventory(broken, INVENTORY)
    row(broken, "syntax.dot")["claims"] = ["S-99"]
    with pytest.raises(features.LedgerError, match="S-99"):
        features.check_against_inventory(broken, INVENTORY)


def test_the_capability_masks_are_nested_and_cover_the_artifact() -> None:
    masks = features.capability_masks(LEDGER)
    assert set(masks["default"]) <= set(masks["gated"])
    features.check_against_artifact(LEDGER, PROGRAM)


def test_an_opcode_no_feature_claims_is_a_refusal() -> None:
    """The direction that would otherwise go unnoticed: the artifact grows an
    opcode, and the ledger has no policy about it at all."""
    broken = copy.deepcopy(LEDGER)
    row(broken, "core.pattern")["capabilities"]["default"] = []
    with pytest.raises(features.LedgerError, match="OpAccept"):
        features.check_against_artifact(broken, PROGRAM)


def test_a_capability_the_artifact_does_not_have_is_a_refusal() -> None:
    broken = copy.deepcopy(LEDGER)
    row(broken, "syntax.atomic")["capabilities"]["gated"] = ["OpAtomicStart"]
    with pytest.raises(features.LedgerError, match="OpAtomicStart"):
        features.check_against_artifact(broken, PROGRAM)


def test_a_wave_two_row_cannot_default_on_an_incomplete_chain() -> None:
    def change(ledger: dict) -> None:
        entry = row(ledger, "syntax.atomic")
        entry.update(
            implementation="complete",
            artifactVersion=2,
            s="complete",
            r="complete",
            i="incomplete",
            claims=["S-8"],
            default=True,
            gated=True,
        )

    assert "syntax.atomic" in str(mutate(change))


def test_a_wave_two_row_cannot_borrow_wave_ones_fallback() -> None:
    def change(ledger: dict) -> None:
        entry = row(ledger, "syntax.atomic")
        entry.update(
            implementation="complete",
            artifactVersion=2,
            s="complete",
            r="complete",
            i="incomplete",
            claims=["S-8"],
            admissionBasis=features.FALLBACK,
            default=True,
            gated=True,
        )

    assert features.FALLBACK in str(mutate(change))


def test_a_boolean_wave_cannot_pass_for_wave_one() -> None:
    """Python makes `bool` an `int`, so `wave: true` equals 1 and would carry
    wave 1's fallback into a wave 2 row without tripping the wave check."""

    def change(ledger: dict) -> None:
        entry = row(ledger, "syntax.atomic")
        entry.update(
            wave=True,
            implementation="complete",
            artifactVersion=2,
            s="complete",
            r="complete",
            i="incomplete",
            claims=["S-8"],
            admissionBasis=features.FALLBACK,
            default=True,
            gated=True,
        )

    assert "Boolean" in str(mutate(change))


def test_a_wave_outside_the_three_is_a_refusal() -> None:
    assert "wave" in str(mutate(lambda ledger: row(ledger, "syntax.dot").update(wave=4)))


def test_an_unadmitted_row_cannot_declare_opcodes_it_will_never_emit() -> None:
    """A capability on a row nothing admits is not harmless: it reads as
    ownership when the artifact's opcodes are checked for a claimant."""

    def change(ledger: dict) -> None:
        entry = row(ledger, "syntax.dot")
        entry.update(default=False, gated=False, i="absent")

    assert "default opcodes" in str(mutate(change))


def test_an_unimplemented_row_cannot_be_gated() -> None:
    assert "admitted" in str(
        mutate(lambda ledger: row(ledger, "syntax.atomic").update(gated=True))
    )


def test_a_default_row_cannot_depend_on_a_gated_one() -> None:
    def change(ledger: dict) -> None:
        row(ledger, "syntax.literal")["dependsOn"] = ["syntax.atomic"]

    assert "syntax.atomic" in str(mutate(change))


def test_a_repeated_key_is_a_refusal() -> None:
    def change(ledger: dict) -> None:
        ledger["features"].append(copy.deepcopy(row(ledger, "syntax.dot")))

    assert "repeated" in str(mutate(change))


def test_an_unknown_field_is_a_refusal() -> None:
    def change(ledger: dict) -> None:
        row(ledger, "syntax.dot")["ship"] = True

    assert "ship" in str(mutate(change))


def test_a_missing_field_is_a_refusal() -> None:
    def change(ledger: dict) -> None:
        del row(ledger, "syntax.dot")["gated"]

    assert "gated" in str(mutate(change))


def test_a_dependency_cycle_is_a_refusal() -> None:
    def change(ledger: dict) -> None:
        row(ledger, "syntax.atomic")["dependsOn"] = ["syntax.quantifier.possessive"]

    assert "cycle" in str(mutate(change))


def test_an_unsorted_capability_list_is_a_refusal() -> None:
    def change(ledger: dict) -> None:
        row(ledger, "syntax.dot")["capabilities"]["default"] = ["OpAnyNoNL", "OpAny"]

    assert "unsorted" in str(mutate(change))


def test_the_reserved_fixture_namespace_cannot_reach_a_real_ledger() -> None:
    def change(ledger: dict) -> None:
        row(ledger, "syntax.dot")["key"] = "test.mock"

    assert features.RESERVED_PREFIX in str(mutate(change))
    allowed = copy.deepcopy(LEDGER)
    row(allowed, "syntax.dot")["key"] = "test.mock"
    features.validate(allowed, allow_reserved=True)


def test_a_ledger_that_is_not_canonical_is_refused(tmp_path) -> None:
    path = tmp_path / "features.json"
    path.write_text(json.dumps(LEDGER))
    with pytest.raises(features.LedgerError, match="canonical"):
        features.load(path)
