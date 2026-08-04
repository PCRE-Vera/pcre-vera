"""Command line access to the differential sweep.

    python -m pcrevera.sweep shard              write the committed shard
    python -m pcrevera.sweep manifest           write a manifest and stop
    python -m pcrevera.sweep run                run one, against pcre2
    python -m pcrevera.sweep replay             one case, in full
    python -m pcrevera.sweep reduce             minimize a run's failures
    python -m pcrevera.sweep promote            minimized cases into the corpus
    python -m pcrevera.sweep gate               read a result document back

`run` is the campaign. It writes four files into its output directory — the
manifest, the results, the coverage table and, when there is anything to say,
the failures — and prints the numbers the LOG wants: the command, the seed, the
manifest hash, the counts and the gate's verdict.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from ..engine.driver import Engine
from ..oracle import conformance
from ..paths import REPO_ROOT, TMP_DIR
from . import campaign, failures, gate, manifest, population, promote, shard
from .checks import DEFAULT_EDGES, run_case
from .population import case as one_case
from .reduce import minimize

DEFAULT_OUT = TMP_DIR / "sweep"


def _log(message: str) -> None:
    print(f"sweep: {message}", file=sys.stderr)


def _progress(done: int, total: int) -> None:
    if done % 50 == 0 or done == total:
        print(f"sweep: {done}/{total} cases", file=sys.stderr)


def _manifest(args: argparse.Namespace):
    if args.manifest:
        return manifest.load(Path(args.manifest))
    return manifest.read(
        manifest.build(
            args.seed,
            structured=args.structured,
            hostile=args.hostile,
            subjects=args.subjects,
            stride=args.stride,
        )
    )


def command_shard(args: argparse.Namespace) -> int:
    shard.PATH.write_text(shard.corpus_text())
    print(f"wrote {shard.PATH.relative_to(REPO_ROOT)}")
    return 0


def command_manifest(args: argparse.Namespace) -> int:
    built = manifest.build(
        args.seed,
        structured=args.structured,
        hostile=args.hostile,
        subjects=args.subjects,
        stride=args.stride,
    )
    out = Path(args.out or DEFAULT_OUT / "manifest.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(manifest.text(built))
    print(f"{out}  {len(built['cases'])} cases  sha256 {manifest.digest(built)}")
    return 0


def command_run(args: argparse.Namespace) -> int:
    held = _manifest(args)
    out = Path(args.out or DEFAULT_OUT)
    out.mkdir(parents=True, exist_ok=True)
    (out / "manifest.json").write_text(manifest.text(held.document))
    _log(f"{len(held.cases)} cases, manifest sha256 {held.digest}")
    report = campaign.run_parallel(
        held,
        jobs=args.jobs,
        oracle=not args.no_oracle,
        edges=args.edges,
        progress=_progress,
    )
    found = failures.identity()
    # The kept regressions ride along with every result document, not only
    # with the committed shard: a runner handed a sweep to replay should be
    # replaying all of it, and a section that is only sometimes there is a
    # section a runner learns to skip.
    (out / "results.json").write_text(
        conformance.text(
            report.document(
                identity=vars(found),
                # Each under the budget its own entry carries, which is the
                # one its failure was found under and the one it goes on
                # guarding under. The record says which, since this document's
                # own budget is a different number.
                regressions=shard.kept(),
                **held.shape,
            )
        )
    )
    (out / "coverage.txt").write_text(gate.table(report.coverage) + "\n")
    if report.findings:
        records = [
            failures.record(
                one,
                _rebuilt(held, one.index),
                subjects=held.shape["subjects"],
                structured=held.shape["structured"],
                budget=held.budget,
                edges=args.edges,
            )
            for one in report.findings
        ]
        failures.write(out / "failures.json", records, found, held.budget, args.edges)
    # A run that found nothing but covered nothing has established nothing, so
    # the gate is part of the exit status rather than something a reader has to
    # notice. A population too small to clear it fails here by design.
    return 0 if _summary(held, report, out) else 1


def _rebuilt(held, index: int):
    for one in held.cases:
        if one.index == index:
            return one
    raise KeyError(f"the manifest has no case {index}")


def _summary(held, report: campaign.Report, out: Path) -> bool:
    """Print what the run established, and say whether it established it."""
    missing = gate.missing(report.coverage)
    print(gate.table(report.coverage))
    print()
    print(f"seed            {held.seed}")
    print(f"manifest        sha256 {held.digest}")
    print(f"cases           {len(held.cases)}")
    print(f"records         {len(report.records)}")
    print(f"findings        {len(report.findings)}")
    print(f"seconds         {report.seconds:.1f}")
    print(f"output          {out}")
    for one in report.findings[:20]:
        print(f"  {one}")
    if missing:
        print("\nthe completion gate is not cleared, never reached:")
        for name in missing:
            print(f"  {name}")
        return False
    print("\nthe completion gate is cleared: everything it asks for was covered.")
    return not report.findings


def command_replay(args: argparse.Namespace) -> int:
    built = one_case(
        args.seed, args.index, subjects=args.subjects, structured=args.structured
    )
    oracle = None if args.no_oracle else campaign.opened(_log)
    budget = {"cost": args.cost, "stack": args.stack, "memory": args.memory}
    outcome = run_case(Engine(), built, budget=budget, oracle=oracle, edges=args.edges)
    print(json.dumps(outcome.record, indent=2, sort_keys=True))
    for one in outcome.findings:
        print(one, file=sys.stderr)
    return 1 if outcome.findings else 0


def command_reduce(args: argparse.Namespace) -> int:
    """Shrink every failure in the file, under the run's own budget.

    The budget and the edge count come out of the file rather than from the
    defaults: a ResourceExceeded is a decline under one budget and a finding
    under another, so shrinking under different limits would be shrinking
    towards a different failure.
    """
    path = Path(args.failures)
    document = conformance.read(path)
    budget = _budget(document)
    edges = document.get("edges", DEFAULT_EDGES)
    oracle = None if args.no_oracle else campaign.opened(_log)
    engine = Engine()
    records = []
    for entry in document["cases"]:
        built = manifest.decode(entry["case"])
        _log(f"reducing case {built.index} ({entry['kind']})")
        smaller = minimize(
            built,
            entry["kind"],
            engine=engine,
            budget=budget,
            oracle=oracle,
            edges=edges,
        )
        records.append({**entry, "minimized": manifest.encode(smaller)})
        print(f"case {built.index}: {built.pattern!r} -> {smaller.pattern!r}")
    failures.write(path, records, failures.Identity(**document["identity"]), budget, edges)
    print(f"wrote {path}")
    return 0


def _budget(document: dict) -> dict[str, int]:
    """The budget a document was produced under, or the default it did not
    bother to write down."""
    return dict(document.get("budget") or manifest.DEFAULT_BUDGET)


def command_promote(args: argparse.Namespace) -> int:
    """The last step of the failure loop: a fixed case joins a corpus.

    Which corpus depends on what disagreed. A compile or match disagreement is
    about the answer, and goes into `oracle/corpus/wave1.json` with pcre2's own
    answer; everything else is about an invariant no semantic corpus checks,
    and goes into `oracle/corpus/sweep-regressions.json`, whose cases are
    replayed through the whole sweep battery. Either way, a case the engine
    still disagrees about is refused rather than committed.
    """
    document = conformance.read(Path(args.failures))
    budget = _budget(document)
    edges = document.get("edges", DEFAULT_EDGES)
    picked = []
    # A case can fail in more than one way, so the class is part of the name
    # and a repeat of both gets a number. Both corpora refuse a duplicate name,
    # and a promotion that produced one would be a promotion that broke the
    # file it was adding to.
    seen: dict[str, int] = {}
    for entry in document["cases"]:
        if "minimized" not in entry:
            _log(f"case {entry['index']} has not been reduced, skipping")
            continue
        built = manifest.decode(entry["minimized"])
        name = f"sweep-{built.seed}-{built.index}-{entry['kind']}"
        seen[name] = seen.get(name, 0) + 1
        if seen[name] > 1:
            name = f"{name}-{seen[name]}"
        picked.append(
            (
                built,
                entry["kind"],
                name,
                f"minimized from the {entry['kind']} disagreement the sweep found "
                f"at seed {built.seed}, index {built.index}",
            )
        )
    if not picked:
        _log("nothing to promote")
        return 1
    for where, names in promote.promote(
        campaign.opened(_log), picked, budget=budget, edges=edges
    ).items():
        for name in names:
            print(f"promoted {name} into the {where} corpus")
    _log("run `make generate` to record the answers of a promoted regression")
    return 0


def command_gate(args: argparse.Namespace) -> int:
    document = conformance.read(Path(args.results))
    coverage = gate.Coverage.of(document["coverage"])
    print(gate.table(coverage))
    missing = gate.missing(coverage)
    for name in missing:
        print(f"never reached: {name}", file=sys.stderr)
    return 1 if missing else 0


def main(argv: list[str]) -> int:
    # The description is a list of commands, and a formatter that reflowed it
    # into a paragraph would make the one thing `--help` is read for unreadable.
    parser = argparse.ArgumentParser(
        prog="python -m pcrevera.sweep",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = parser.add_subparsers(dest="command", required=True)

    def population_arguments(one: argparse.ArgumentParser) -> None:
        """The shape of the population, defaulted where a case is built.

        A default that drifted between two subcommands would have `replay`
        rebuild a different case than the one `run` found, which is the whole
        thing the replay command exists not to do.
        """
        one.add_argument("--seed", type=int, default=manifest.DEFAULT_SEED)
        one.add_argument("--structured", type=int, default=population.STRUCTURED)
        one.add_argument("--hostile", type=int, default=population.HOSTILE)
        one.add_argument("--subjects", type=int, default=population.SUBJECTS)
        one.add_argument("--stride", type=int, default=1)

    sub.add_parser("shard", help="write the committed shard").set_defaults(
        run=command_shard
    )

    built = sub.add_parser("manifest", help="write a manifest and stop")
    population_arguments(built)
    built.add_argument("--out")
    built.set_defaults(run=command_manifest)

    running = sub.add_parser("run", help="run a sweep against pcre2")
    population_arguments(running)
    running.add_argument("--manifest", help="run this manifest rather than generating one")
    running.add_argument("--jobs", type=int, default=1)
    running.add_argument("--edges", type=int, default=DEFAULT_EDGES)
    running.add_argument("--no-oracle", action="store_true")
    running.add_argument("--out")
    running.set_defaults(run=command_run)

    again = sub.add_parser("replay", help="one case, in full")
    again.add_argument("--seed", type=int, default=manifest.DEFAULT_SEED)
    again.add_argument("--index", type=int, required=True)
    again.add_argument("--subjects", type=int, default=population.SUBJECTS)
    again.add_argument("--structured", type=int, default=population.STRUCTURED)
    again.add_argument("--edges", type=int, default=DEFAULT_EDGES)
    for name, value in manifest.DEFAULT_BUDGET.items():
        again.add_argument(f"--{name}", type=int, default=value)
    again.add_argument("--no-oracle", action="store_true")
    again.set_defaults(run=command_replay)

    smaller = sub.add_parser("reduce", help="minimize the failures of a run")
    smaller.add_argument("failures")
    smaller.add_argument("--no-oracle", action="store_true")
    smaller.set_defaults(run=command_reduce)

    moved = sub.add_parser("promote", help="minimized cases into the corpus")
    moved.add_argument("failures")
    moved.set_defaults(run=command_promote)

    verdict = sub.add_parser("gate", help="read a result document back")
    verdict.add_argument("results")
    verdict.set_defaults(run=command_gate)

    args = parser.parse_args(argv)
    return args.run(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
