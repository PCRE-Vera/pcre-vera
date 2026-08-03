"""Building the pinned pcre2, and the shim that talks to it.

The build is keyed by everything that could change its result: the pin file,
the shim source, the recipe in this module, and the compiler. Change any of
them and the next build lands in a different directory, so a stale object file
can never pass for the reference. A build that finishes writes a manifest
recording what it produced, including the configuration read back out of the
linked library; a build that fails leaves no manifest, so the next run starts
over. Picking a cached build back up re-establishes those facts rather than
trusting the directory name (see `reuse`), and `audit` does the fuller version
from disk.

Only the 8-bit library is built, not pcre2test or pcre2grep, which takes a
couple of seconds rather than a minute.
"""

from __future__ import annotations

import functools
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from ..paths import SHIM_SOURCE, oracle_cache
from . import chartables
from . import pin as pin_module
from .client import Oracle
from .pin import Pin

DOWNLOAD_TIMEOUT_SECONDS = 300

SHIM_NAME = "pcre2shim"
MANIFEST_NAME = "manifest.json"
DOWNLOADS = "downloads"


Logger = Callable[[str], None] | None


class BuildError(RuntimeError):
    """The oracle could not be built."""


@dataclass(frozen=True)
class OracleBuild:
    build_id: str
    directory: Path
    source_dir: Path
    shim: Path
    manifest_path: Path
    manifest: dict[str, object]


def _describe(
    pin: Pin, identifier: str, directory: Path, manifest: dict[str, object]
) -> OracleBuild:
    """Where everything sits inside a build directory, said once."""
    return OracleBuild(
        build_id=identifier,
        directory=directory,
        source_dir=directory / pin.source_directory,
        shim=directory / SHIM_NAME,
        manifest_path=directory / MANIFEST_NAME,
        manifest=manifest,
    )


def tarball_path(pin: Pin) -> Path:
    return oracle_cache() / DOWNLOADS / pin.tarball


def compiler() -> str:
    """The C compiler the build uses, honouring CC as every build system does."""
    return os.environ.get("CC", "cc")


def compiler_identity() -> str:
    """Which compiler, and which version of it, as one auditable line.

    Part of the build key: the same sources built by a different compiler are a
    different binary, and a cache directory named after the sources alone would
    hand that binary back without a word. Memoized on the compiler's name rather
    than on nothing, so changing CC in a running process is answered honestly.
    """
    return _identify(compiler())


@functools.lru_cache(maxsize=None)
def _identify(name: str) -> str:
    try:
        result = subprocess.run(
            [name, "--version"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True
        )
    except OSError:
        return f"{name}: unavailable"
    first_line = result.stdout.splitlines()[0] if result.stdout else ""
    return f"{name}: {first_line}"


def file_digest(path: Path) -> str:
    """SHA-256 of a file, streamed: the tarball is megabytes."""
    with open(path, "rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def _recipe_digest() -> str:
    """This module's own source. The recipe is code, so the code is the version.

    A hand-maintained version number is a promise to remember, and forgetting it
    once means a changed recipe silently reusing a build made by the old one.
    """
    return file_digest(Path(__file__))


def build_id(pin: Pin) -> str:
    """A short digest over everything the build depends on."""
    digest = hashlib.sha256()
    digest.update(b"pcrevera-oracle\0")
    digest.update(_recipe_digest().encode() + b"\0")
    digest.update(pin.digest.encode() + b"\0")
    digest.update(file_digest(SHIM_SOURCE).encode() + b"\0")
    digest.update(compiler_identity().encode())
    return digest.hexdigest()[:16]


def _verify_digest(path: Path, expected: str, what: str) -> None:
    digest = file_digest(path)
    if digest != expected:
        raise BuildError(f"{what} has sha256 {digest}, pin expects {expected}")


def _download(pin: Pin, cache: Path, log: Logger) -> Path:
    """The pinned tarball, in the shared cache, verified.

    It arrives through a temporary file of this process's own and is moved into
    place in one step, whether it came off the network or off a local copy. The
    hash is checked before that move, so the shared path never holds anything
    but the pinned bytes, and a second process reading it can never catch a
    half-written file.
    """
    downloads = cache / DOWNLOADS
    downloads.mkdir(parents=True, exist_ok=True)
    tarball = downloads / pin.tarball

    if tarball.exists():
        try:
            _verify_digest(tarball, pin.sha256, str(tarball))
            return tarball
        except BuildError:
            # Something not ours put a wrong file there. Fetch again, and
            # tolerate another process having just done the same.
            tarball.unlink(missing_ok=True)

    local = os.environ.get("PCREVERA_PCRE2_TARBALL")
    handle = tempfile.NamedTemporaryFile(dir=downloads, delete=False)
    partial_path = Path(handle.name)
    try:
        with handle:
            if local:
                _say(log, f"copying {local}")
                with open(local, "rb") as source:
                    shutil.copyfileobj(source, handle)
            else:
                _say(log, f"fetching {pin.url}")
                with urllib.request.urlopen(pin.url, timeout=DOWNLOAD_TIMEOUT_SECONDS) as response:
                    shutil.copyfileobj(response, handle)
        _verify_digest(partial_path, pin.sha256, f"{pin.tarball} as fetched")
    except BaseException:
        partial_path.unlink(missing_ok=True)
        raise

    partial_path.replace(tarball)
    return tarball


def _extract(pin: Pin, tarball: Path, directory: Path, log: Logger) -> Path:
    source_dir = directory / pin.source_directory
    if source_dir.exists():
        shutil.rmtree(source_dir)
    _say(log, f"unpacking {tarball.name}")
    with tarfile.open(tarball, "r:bz2") as archive:
        archive.extractall(directory, filter="data")
    if not source_dir.is_dir():
        raise BuildError(f"{pin.tarball} did not unpack into {pin.source_directory}")

    _verify_digest(
        source_dir / pin.chartables_source,
        pin.chartables_source_sha256,
        pin.chartables_source,
    )
    return source_dir


def _run(command: list[str], cwd: Path, log: Logger, step: str) -> None:
    _say(log, f"{step}: {' '.join(command[:2])} ...")
    result = subprocess.run(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    (cwd / f"pcrevera-{step}.log").write_text(result.stdout)
    if result.returncode != 0:
        tail = "\n".join(result.stdout.splitlines()[-30:])
        raise BuildError(f"{step} failed with status {result.returncode}:\n{tail}")


def _build_library(pin: Pin, source_dir: Path, log: Logger) -> None:
    _run(
        ["./configure", *pin.configure, f"CC={compiler()}", f"CFLAGS={pin.cflags}"],
        source_dir,
        log,
        "configure",
    )
    jobs = os.cpu_count() or 1
    _run(["make", f"-j{jobs}", pin.make_target], source_dir, log, "make")

    library = source_dir / pin.library
    if not library.is_file():
        raise BuildError(f"the build did not produce {pin.library}")


def _build_shim(pin: Pin, source_dir: Path, directory: Path, log: Logger) -> Path:
    shim = directory / SHIM_NAME
    _say(log, "compiling the shim")
    _run(
        [
            compiler(),
            "-O2",
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-o",
            str(shim),
            str(SHIM_SOURCE),
            f"-I{source_dir / pin.include_dir}",
            str(source_dir / pin.library),
        ],
        directory,
        log,
        "shim",
    )
    return shim


def _read_back_configuration(pin: Pin, shim: Path) -> dict[str, object]:
    with Oracle(shim, pin.limits) as oracle:
        return oracle.config()


def _say(log: Logger, message: str) -> None:
    if log is not None:
        log(message)


def problems(pin: Pin, build: OracleBuild, *, deep: bool = False) -> list[str]:
    """Everything that says this build is not the reference build any more.

    One list of invariants with two depths, rather than two lists that drift.
    The shallow set runs every time a cached build is picked up, so it stays
    cheap: the manifest describes this pin, the extracted tree still holds the
    library and the pinned character table source, the binary is the one the
    manifest recorded, and the library it links still reports the pinned
    configuration. The deep set adds what only an audit needs to pay for: the
    cached tarball, the compiler, and the table bytes the library actually uses.

    Neither depth re-verifies the rest of the extracted tree against the
    tarball. The tables are the part of that tree whose contents reach into
    pcre2's observable behavior; the rest is covered by the configuration
    readback and by the build key.
    """
    found: list[str] = []
    manifest = build.manifest

    if manifest.get("build_id") != build.build_id:
        found.append(f"the manifest records build {manifest.get('build_id')!r}")
    if manifest.get("pin_sha256") != pin.digest:
        found.append(f"the manifest was written against pin {manifest.get('pin_sha256')!r}")

    if deep:
        tarball = tarball_path(pin)
        if not tarball.is_file():
            found.append(f"the pinned tarball is gone from the cache: {tarball}")
        else:
            digest = file_digest(tarball)
            if digest != pin.sha256:
                found.append(f"the cached tarball has sha256 {digest}, pin expects {pin.sha256}")
        if manifest.get("compiler") != compiler_identity():
            found.append(
                f"the build used {manifest.get('compiler')!r}, "
                f"this machine has {compiler_identity()!r}"
            )

    if not (build.source_dir / pin.library).is_file():
        found.append(f"the built library is gone: {build.source_dir / pin.library} is missing")

    shipped_source = build.source_dir / pin.chartables_source
    shipped: bytes | None = None
    if not shipped_source.is_file():
        found.append(f"the source tree is gone: {shipped_source} is missing")
    else:
        digest = file_digest(shipped_source)
        if digest != pin.chartables_source_sha256:
            found.append(
                f"{pin.chartables_source} has sha256 {digest}, "
                f"pin expects {pin.chartables_source_sha256}"
            )
        elif deep:
            shipped = chartables.parse(shipped_source)

    recorded = manifest.get("binary_sha256")
    try:
        binary = file_digest(build.shim)
    except OSError as error:
        found.append(f"the shim binary cannot be read: {error}")
        return found
    if binary != recorded:
        found.append(f"the shim binary has sha256 {binary}, its manifest recorded {recorded}")

    try:
        observed = _read_back_configuration(pin, build.shim)
    except Exception as error:
        found.append(f"the shim does not answer: {error}")
        return found

    found.extend(pin_module.check_configuration(observed, pin))
    if shipped is not None and observed.get("tables") != shipped:
        found.append("the linked library does not use the character tables the release ships")

    return found


def audit(pin: Pin, build: OracleBuild) -> list[str]:
    """The full set of checks, for `verify`. One line per disagreement."""
    return problems(pin, build, deep=True)


def reuse(pin: Pin, directory: Path, identifier: str | None = None) -> OracleBuild | None:
    """A cached build, if it is still the reference build, otherwise None.

    A directory name derived from the pin says which build was meant to be here,
    not what is here now, so reuse re-establishes what the original build
    established. Anything less would make the cache a way around the pin.
    """
    identifier = identifier if identifier is not None else build_id(pin)
    try:
        manifest = json.loads((directory / MANIFEST_NAME).read_text())
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(manifest, dict):
        # Well-formed JSON that is not a manifest is still not a manifest.
        return None

    build = _describe(pin, identifier, directory, manifest)
    return None if problems(pin, build) else build


def _retire(directory: Path) -> None:
    """Get a directory out of the way, tolerating someone else doing the same."""
    if not directory.exists():
        return
    aside = Path(tempfile.mkdtemp(dir=directory.parent, prefix=".retired-"))
    try:
        directory.rename(aside / directory.name)
    except OSError:
        pass
    finally:
        shutil.rmtree(aside, ignore_errors=True)


def ensure(*, rebuild: bool = False, log: Logger = None, pin: Pin | None = None) -> OracleBuild:
    """Return a usable oracle, building it first if there is not one already.

    The build happens in a staging directory of its own and is moved into place
    in one step at the end, so two of these running against one cache — two
    developers on a shared machine, or one Makefile invoked with -j — never
    unpack over each other's source tree. Whoever finishes second finds the
    other's build already published and uses it, having wasted nothing but its
    own time.
    """
    pin = pin or pin_module.load()
    cache = oracle_cache()
    identifier = build_id(pin)
    directory = cache / f"pcre2-{pin.version}-{identifier}"

    if rebuild:
        _retire(directory)

    if (directory / MANIFEST_NAME).is_file():
        reusable = reuse(pin, directory, identifier)
        if reusable is not None:
            return reusable
        _say(log, "the cached build is not the reference build any more; rebuilding")
        _retire(directory)

    cache.mkdir(parents=True, exist_ok=True)
    tarball = _download(pin, cache, log)
    staging = Path(tempfile.mkdtemp(dir=cache, prefix=f".building-{identifier}-"))
    try:
        source_dir = _extract(pin, tarball, staging, log)
        _build_library(pin, source_dir, log)
        shim = _build_shim(pin, source_dir, staging, log)

        observed = _read_back_configuration(pin, shim)
        mismatches = pin_module.check_configuration(observed, pin)
        if mismatches:
            raise BuildError(
                "the library that got built is not the reference build:\n  "
                + "\n  ".join(mismatches)
            )

        manifest = {
            "build_id": identifier,
            "pin_sha256": pin.digest,
            "pcre2_version": pin.version,
            "tarball_sha256": pin.sha256,
            "chartables_source_sha256": pin.chartables_source_sha256,
            "configure": list(pin.configure),
            "cflags": pin.cflags,
            "shim_source_sha256": file_digest(SHIM_SOURCE),
            "recipe_sha256": _recipe_digest(),
            "compiler": compiler_identity(),
            "binary_sha256": file_digest(shim),
            "observed": readable_configuration(observed),
        }
        (staging / MANIFEST_NAME).write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n"
        )

        try:
            staging.rename(directory)
        except OSError:
            # Another build published first. Its answer is as good as ours.
            shutil.rmtree(staging, ignore_errors=True)
            reusable = reuse(pin, directory, identifier)
            if reusable is None:
                raise BuildError(f"another build published something unusable at {directory}")
            _say(log, f"oracle ready at {reusable.shim}")
            return reusable
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise

    built = _describe(pin, identifier, directory, manifest)
    _say(log, f"oracle ready at {built.shim}")
    return built


def readable_configuration(observed: dict[str, object]) -> dict[str, object]:
    """The configuration as text: the tables as a digest, not 1088 bytes.

    One rendering, used by the manifest and by the CLI, so a new bytes-valued
    field is handled once.
    """
    recorded: dict[str, object] = {}
    for key, value in observed.items():
        if key == "tables" and isinstance(value, bytes):
            recorded["tables_sha256"] = hashlib.sha256(value).hexdigest()
        elif isinstance(value, bytes):
            recorded[key] = value.decode("ascii", "replace")
        else:
            recorded[key] = value
    return recorded


def open_oracle(build: OracleBuild | None = None, pin: Pin | None = None) -> Oracle:
    """A running oracle, from a build if you have one.

    The one place that knows how an oracle is opened, so that adding a timeout
    or a version negotiation is one edit rather than one per caller.
    """
    pin = pin or pin_module.load()
    build = build or ensure(pin=pin)
    return Oracle(build.shim, pin.limits)
