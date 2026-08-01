"""M0: the parts of the project exist and hang together."""

from __future__ import annotations

import pcretruste
from pcretruste import paths


def test_package_imports():
    assert pcretruste.__version__


def test_repository_root_is_the_checkout():
    assert (paths.REPO_ROOT / "pyproject.toml").is_file()
    assert (paths.REPO_ROOT / "DESIGN.md").is_file()


def test_every_part_of_the_pipeline_has_a_place():
    for path in (
        paths.PIN_PATH,
        paths.SHIM_SOURCE,
        paths.CORPUS_DIR / "seed.json",
        paths.LEAN_DIR / "lakefile.toml",
        paths.LEAN_DIR / "lean-toolchain",
        paths.GEN_DIR / "go" / "go.mod",
        paths.GEN_DIR / "js" / "package.json",
    ):
        assert path.is_file(), f"{path} is missing"


def test_scratch_directory_is_not_committed():
    gitignore = (paths.REPO_ROOT / ".gitignore").read_text().split()
    assert "tmp/" in gitignore
