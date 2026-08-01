"""Reproducibility: the oracle we run is the oracle the pin describes.

DESIGN.md section 2.3 makes one exact libpcre2 build the arbiter of what
"correct PCRE" means. These tests are what stops that from being a claim in a
document: the tarball is the pinned one, the character tables are the shipped
ones, and the library that got linked reports the pinned configuration back.
"""

from __future__ import annotations

import concurrent.futures
import dataclasses
import hashlib
import json
import re
import shutil
import tomllib

import tomli_w
from pathlib import Path

import pytest

from pcretruste.oracle import Pin, check_configuration
from pcretruste.oracle import build as build_module
from pcretruste.oracle import pin as pin_module
from pcretruste.oracle import chartables
from pcretruste.paths import oracle_cache

HEX_DIGEST = re.compile(r"^[0-9a-f]{64}$")


def test_oracle_pin_is_wellformed(pin: Pin):
    assert pin.version in pin.release_tag
    assert pin.tarball in pin.url
    assert HEX_DIGEST.match(pin.sha256)
    assert HEX_DIGEST.match(pin.chartables_source_sha256)
    assert HEX_DIGEST.match(str(pin.expect["tables_sha256"]))
    assert pin.configure, "a pin with no configure flags pins nothing"


def test_oracle_pin_forbids_rebuilding_the_character_tables(pin: Pin):
    """Rebuilding them would make the reference depend on the build machine's locale."""
    assert "--disable-rebuild-chartables" in pin.configure
    assert "--enable-rebuild-chartables" not in pin.configure


def test_oracle_pin_forbids_the_jit(pin: Pin):
    assert "--disable-jit" in pin.configure
    assert pin.expect["jit"] == 0


def test_oracle_tarball_matches_the_pin(pin: Pin, oracle_build):
    tarball = oracle_cache() / "downloads" / pin.tarball
    assert tarball.is_file()
    assert hashlib.sha256(tarball.read_bytes()).hexdigest() == pin.sha256


def test_oracle_chartables_source_matches_the_pin(pin: Pin, oracle_build):
    shipped = oracle_build.source_dir / pin.chartables_source
    assert hashlib.sha256(shipped.read_bytes()).hexdigest() == pin.chartables_source_sha256


def test_oracle_configuration_matches_the_pin(pin: Pin, oracle):
    problems = check_configuration(oracle.config(), pin)
    assert problems == [], "\n".join(problems)


def test_oracle_uses_the_character_tables_the_release_ships(pin: Pin, oracle, oracle_build):
    """The strong form of the tables check: same bytes, not just two hashes that agree.

    The shim recovers the tables the linked library actually uses; this compares
    them against the ones parsed straight out of the release's own C source.
    """
    shipped = chartables.parse(oracle_build.source_dir / pin.chartables_source)
    linked = oracle.config()["tables"]

    assert len(shipped) == pin.expect["tables_length"]
    assert linked == shipped


def test_oracle_manifest_records_what_was_built(pin: Pin, oracle_build):
    manifest = oracle_build.manifest
    assert manifest["pin_sha256"] == pin.digest
    assert manifest["tarball_sha256"] == pin.sha256
    assert manifest["configure"] == list(pin.configure)
    assert manifest["observed"]["tables_sha256"] == pin.expect["tables_sha256"]


def test_oracle_build_is_keyed_by_everything_it_depends_on(pin: Pin, oracle_build):
    """Asking again gives the same build, and editing the pin would not."""
    again = build_module.ensure(pin=pin)
    assert again.build_id == oracle_build.build_id
    assert again.shim == oracle_build.shim

    edited = dataclasses.replace(pin, digest="0" * 64)
    assert build_module.build_id(edited) != build_module.build_id(pin)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("jit", 1),
        ("newline", 3),
        ("bsr", 2),
        ("unicode", 0),
        ("link_size", 3),
        ("tables", b"\x00" * 1088),
        ("applied_match_limit", 1),
    ],
)
def test_oracle_pin_check_notices_a_different_build(pin: Pin, oracle, field, value):
    """The checker has to complain, or none of the checks above mean anything."""
    doctored = dict(oracle.config())
    doctored[field] = value
    assert check_configuration(doctored, pin), f"a wrong {field} went unnoticed"


def test_oracle_refuses_a_tarball_that_is_not_the_pinned_one(pin: Pin, tmp_path, monkeypatch):
    """Substituting the source is the one thing a pin has to catch."""
    impostor = tmp_path / "pcre2.tar.bz2"
    impostor.write_bytes(b"this is not pcre2")
    monkeypatch.setenv("PCRETRUSTE_ORACLE_CACHE", str(tmp_path / "cache"))
    monkeypatch.setenv("PCRETRUSTE_PCRE2_TARBALL", str(impostor))

    with pytest.raises(build_module.BuildError, match="sha256"):
        build_module.ensure(pin=pin)


def _cached_build(pin, oracle_build, directory):
    """A complete cache entry, so a rejection is never for a missing piece.

    The source tree is shared by symlink rather than copied: the checks read it,
    they do not write to it, and copying twenty megabytes per test to prove a
    point about a tampered binary would be silly.
    """
    directory.mkdir(parents=True, exist_ok=True)
    (directory / pin.source_directory).symlink_to(oracle_build.source_dir, True)
    shutil.copy2(oracle_build.shim, directory / build_module.SHIM_NAME)
    shutil.copy2(oracle_build.manifest_path, directory / build_module.MANIFEST_NAME)
    return directory


def _retag_manifest(directory, **changes):
    path = directory / build_module.MANIFEST_NAME
    manifest = json.loads(path.read_text())
    manifest.update(changes)
    path.write_text(json.dumps(manifest))


def test_oracle_reuses_a_cache_that_is_still_the_reference(pin: Pin, oracle_build):
    reused = build_module.reuse(pin, oracle_build.directory)
    assert reused is not None
    assert reused.shim == oracle_build.shim


def test_oracle_reuses_a_complete_copy_of_a_cache(pin: Pin, oracle_build, tmp_path):
    """The positive case the tampering below is variations on."""
    directory = _cached_build(pin, oracle_build, tmp_path / "build")
    assert build_module.reuse(pin, directory, oracle_build.build_id) is not None


def _remove_the_source_tree(pin, oracle_build, directory):
    (directory / pin.source_directory).unlink()


def _change_the_binary(pin, oracle_build, directory):
    shim = directory / build_module.SHIM_NAME
    shim.write_bytes(shim.read_bytes() + b"\x00")


def _substitute_the_binary(pin, oracle_build, directory):
    """An impostor that speaks the protocol, with the manifest hash to match.

    Getting past the hash is not enough: only asking it for the library
    configuration catches it.
    """
    shim = directory / build_module.SHIM_NAME
    shim.write_text(
        "#!/bin/sh\n"
        "while IFS= read -r line; do\n"
        '  case "$line" in\n'
        "    hello) printf 'hello 1 5:31302e3437\\n' ;;\n"
        "    quit) printf 'bye\\n'; exit 0 ;;\n"
        "    *) printf 'config protocol=1\\n' ;;\n"
        "  esac\n"
        "done\n"
    )
    shim.chmod(0o755)
    _retag_manifest(directory, binary_sha256=hashlib.sha256(shim.read_bytes()).hexdigest())


def _claim_another_pin(pin, oracle_build, directory):
    _retag_manifest(directory, pin_sha256="0" * 64)


def _claim_another_build(pin, oracle_build, directory):
    _retag_manifest(directory, build_id="0" * 16)


@pytest.mark.parametrize(
    "tamper",
    [
        _remove_the_source_tree,
        _change_the_binary,
        _substitute_the_binary,
        _claim_another_pin,
        _claim_another_build,
    ],
    ids=lambda tamper: tamper.__name__.strip("_"),
)
def test_oracle_refuses_a_cache_that_changed(pin: Pin, oracle_build, tmp_path, tamper):
    """A directory named after the pin says what was meant to be there."""
    directory = _cached_build(pin, oracle_build, tmp_path / "build")
    tamper(pin, oracle_build, directory)

    assert build_module.reuse(pin, directory, oracle_build.build_id) is None


def test_oracle_audit_is_clean_for_the_build_in_use(pin: Pin, oracle_build):
    assert build_module.audit(pin, oracle_build) == []


def test_oracle_audit_notices_a_source_tree_that_no_longer_matches(
    pin: Pin, oracle_build, tmp_path
):
    """The audit reads the tree the build came from, so damaging it has to show."""
    fake_source = tmp_path / pin.source_directory
    (fake_source / Path(pin.chartables_source).parent).mkdir(parents=True)
    (fake_source / pin.chartables_source).write_text("not the shipped tables\n")
    damaged = dataclasses.replace(oracle_build, source_dir=fake_source)

    problems = build_module.audit(pin, damaged)
    assert any(pin.chartables_source in problem for problem in problems)


def _pin_with(tmp_path, transform):
    """The real pin, with one thing changed."""
    document = tomllib.loads(pin_module.PIN_PATH.read_text())
    transform(document)
    path = tmp_path / "pin.toml"
    path.write_text(tomli_w.dumps(document))
    return path


@pytest.mark.parametrize("field", sorted(pin_module.EXPECT_TYPES))
def test_oracle_pin_must_say_what_to_expect_for_every_field(tmp_path, field):
    """Dropping a field would silently drop the check that field stands for."""
    path = _pin_with(tmp_path, lambda document: document["expect"].pop(field))
    with pytest.raises(ValueError, match=field):
        pin_module.load(path)


@pytest.mark.parametrize("section", pin_module.TOP_LEVEL_SECTIONS)
def test_oracle_pin_refuses_a_field_nothing_reads(tmp_path, section):
    """A misspelled field would otherwise look pinned while checking nothing."""
    path = _pin_with(tmp_path, lambda document: document[section].update({"jitt": 0}))
    with pytest.raises(ValueError, match="jitt"):
        pin_module.load(path)


def test_oracle_pin_refuses_a_section_nothing_reads(tmp_path):
    path = _pin_with(tmp_path, lambda document: document.update({"extra": {"a": 1}}))
    with pytest.raises(ValueError, match="extra"):
        pin_module.load(path)


@pytest.mark.parametrize(
    ("section", "field", "value"),
    [
        ("source", "sha256", 47),
        ("source", "version", 10.47),
        ("build", "cflags", ["-O2"]),
        ("build", "configure", "--disable-jit"),
        ("limits", "match_limit", "50000000"),
        ("limits", "depth_limit", True),
        ("expect", "jit", "0"),
        ("expect", "newline", 2),
    ],
)
def test_oracle_pin_refuses_a_field_of_the_wrong_type(tmp_path, section, field, value):
    """`sha256 = 47` is a mistake, not a number to be turned into a string."""
    path = _pin_with(tmp_path, lambda document: document[section].update({field: value}))
    with pytest.raises(ValueError, match=field):
        pin_module.load(path)


@pytest.mark.parametrize("section", pin_module.TOP_LEVEL_SECTIONS)
def test_oracle_pin_needs_every_section(tmp_path, section):
    path = _pin_with(tmp_path, lambda document: document.pop(section))
    with pytest.raises(ValueError, match=section):
        pin_module.load(path)


def test_oracle_build_is_keyed_by_the_compiler(pin: Pin, monkeypatch):
    """The same sources built by another compiler are another binary."""
    before = build_module.build_id(pin)
    monkeypatch.setenv("CC", "/usr/bin/false")
    assert build_module.build_id(pin) != before


def test_oracle_audit_notices_a_build_made_by_another_compiler(pin: Pin, oracle_build):
    elsewhere = dataclasses.replace(
        oracle_build, manifest={**oracle_build.manifest, "compiler": "cc: something else"}
    )
    assert any("compiler" in problem or "cc:" in problem
               for problem in build_module.audit(pin, elsewhere))


def test_oracle_audit_reports_a_shim_that_cannot_run(pin: Pin, oracle_build, tmp_path):
    """A broken build has to come back as a failed audit, not a traceback."""
    missing = dataclasses.replace(oracle_build, shim=tmp_path / "not-here")
    problems = build_module.audit(pin, missing)
    assert problems and any("shim" in problem for problem in problems)


def _build_concurrently(pin: Pin, count: int) -> list[build_module.OracleBuild]:
    """Run `count` cold builds at once, and insist every one of them worked."""
    with concurrent.futures.ThreadPoolExecutor(max_workers=count) as pool:
        futures = [pool.submit(build_module.ensure, pin=pin) for _ in range(count)]
        # .result() re-raises whatever the build raised, in this thread.
        return [future.result(timeout=600) for future in futures]


def test_oracle_builds_concurrently_into_one_cache(pin: Pin, oracle_build, tmp_path, monkeypatch):
    """Two cold builds sharing a cache used to unpack over each other's sources.

    Both must finish with a usable oracle: one publishes, the other finds it
    published and takes it. The tarball is seeded from the cache we already have
    so this stays offline.
    """
    cache = tmp_path / "cache"
    (cache / "downloads").mkdir(parents=True)
    tarball = oracle_cache() / "downloads" / pin.tarball
    shutil.copy2(tarball, cache / "downloads" / pin.tarball)
    monkeypatch.setenv("PCRETRUSTE_ORACLE_CACHE", str(cache))

    results = _build_concurrently(pin, 2)

    assert results[0].shim == results[1].shim
    assert build_module.audit(pin, results[0]) == []


@pytest.mark.parametrize("schema", [True, 1.0, "1", 2])
def test_oracle_pin_schema_must_be_the_exact_number(tmp_path, schema):
    """`true` and `1.0` both equal 1 in Python, and neither is a schema."""
    path = _pin_with(tmp_path, lambda document: document.update({"schema": schema}))
    with pytest.raises(ValueError, match="schema"):
        pin_module.load(path)


def test_oracle_pin_must_state_its_schema(tmp_path):
    path = _pin_with(tmp_path, lambda document: document.pop("schema"))
    with pytest.raises(ValueError, match="schema"):
        pin_module.load(path)


def test_oracle_copies_a_local_tarball_into_place_in_one_step(
    pin: Pin, oracle_build, tmp_path, monkeypatch
):
    """The offline path shares the cache too, so it cannot write there directly.

    Three cold builds against an empty cache, all taking the tarball from a
    local copy: with a plain copy into the shared path they can read and unlink
    each other's half-written file.
    """
    cache = tmp_path / "cache"
    local = tmp_path / "pcre2.tar.bz2"
    shutil.copy2(oracle_cache() / "downloads" / pin.tarball, local)
    monkeypatch.setenv("PCRETRUSTE_ORACLE_CACHE", str(cache))
    monkeypatch.setenv("PCRETRUSTE_PCRE2_TARBALL", str(local))

    results = _build_concurrently(pin, 3)

    assert build_module.audit(pin, results[0]) == []
    assert not list((cache / "downloads").glob("tmp*")), "a temporary download was left behind"


@pytest.mark.parametrize("manifest", ["[]", '"manifest"', "17", "null"])
def test_oracle_refuses_a_manifest_that_is_not_one(pin: Pin, oracle_build, tmp_path, manifest):
    """Well-formed JSON that is not a manifest still has to mean "rebuild"."""
    directory = _cached_build(pin, oracle_build, tmp_path / "build")
    (directory / build_module.MANIFEST_NAME).write_text(manifest)

    assert build_module.reuse(pin, directory, oracle_build.build_id) is None
