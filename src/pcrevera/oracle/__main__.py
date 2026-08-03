"""Command line access to the oracle, for building it and looking at it.

    python -m pcrevera.oracle build      build if there is nothing usable yet
    python -m pcrevera.oracle rebuild    build again from scratch
    python -m pcrevera.oracle verify     check the build against the pin
    python -m pcrevera.oracle config     print the library configuration
    python -m pcrevera.oracle corpus     run the seed corpus
    python -m pcrevera.oracle match ...  ask pcre2 about one pattern
"""

from __future__ import annotations

import argparse
import sys

from . import build as build_module
from . import corpus as corpus_module
from . import pin as pin_module
from .client import OracleError
from .protocol import ProtocolError


def _log(message: str) -> None:
    print(f"oracle: {message}", file=sys.stderr)


def _build(rebuild: bool = False) -> build_module.OracleBuild:
    return build_module.ensure(rebuild=rebuild, log=_log)


def command_build(args: argparse.Namespace) -> int:
    built = _build(args.rebuild)
    print(built.shim)
    return 0


def command_verify(args: argparse.Namespace) -> int:
    pin = pin_module.load()
    built = _build()
    problems = build_module.audit(pin, built)

    print(f"pin        {pin.path}")
    print(f"pcre2      {pin.release_tag} ({pin.sha256})")
    print(f"build      {built.directory}")
    print(f"shim       {built.shim}")
    if problems:
        print("\nthe build does not match the pin:")
        for problem in problems:
            print(f"  {problem}")
        return 1
    print(
        "\nthe build matches the pin: same tarball, same character tables, "
        "same binary, same configuration."
    )
    return 0


def command_config(args: argparse.Namespace) -> int:
    with build_module.open_oracle(_build()) as oracle:
        configuration = build_module.readable_configuration(oracle.config())
    for key, value in configuration.items():
        print(f"{key} = {value}")
    return 0


def command_corpus(args: argparse.Namespace) -> int:
    corpus = corpus_module.load()
    with build_module.open_oracle(_build()) as oracle:
        failures = corpus_module.check(oracle, corpus)
    for case, complaint in failures:
        print(f"FAIL {case.name}: {complaint}")
    print(
        f"{len(corpus.cases) - len(failures)}/{len(corpus.cases)} cases from "
        f"{corpus.path} agree with pcre2"
    )
    return 1 if failures else 0


def command_match(args: argparse.Namespace) -> int:
    with build_module.open_oracle(_build()) as oracle:
        outcome = oracle.match(
            args.pattern.encode("latin-1"),
            args.subject.encode("latin-1"),
            start=args.start,
            options=tuple(args.option),
            match_options=tuple(args.match_option),
        )
    print(outcome)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="pcrevera.oracle", description=__doc__)
    subcommands = parser.add_subparsers(required=True)

    # Each subcommand carries its own handler, so there is one list of commands
    # rather than two that have to be kept in step.
    subcommands.add_parser("build", help="build the oracle if needed").set_defaults(
        handler=command_build, rebuild=False
    )
    subcommands.add_parser("rebuild", help="build the oracle from scratch").set_defaults(
        handler=command_build, rebuild=True
    )
    subcommands.add_parser("verify", help="check the build against the pin").set_defaults(
        handler=command_verify
    )
    subcommands.add_parser("config", help="print the library configuration").set_defaults(
        handler=command_config
    )
    subcommands.add_parser("corpus", help="run the seed corpus").set_defaults(
        handler=command_corpus
    )

    match = subcommands.add_parser("match", help="ask pcre2 about one pattern")
    match.set_defaults(handler=command_match)
    match.add_argument("pattern")
    match.add_argument("subject")
    match.add_argument("--start", type=int, default=0)
    match.add_argument("--option", action="append", default=[])
    match.add_argument("--match-option", action="append", default=[], dest="match_option")

    args = parser.parse_args(argv)
    try:
        return args.handler(args)
    except (build_module.BuildError, OracleError, ProtocolError, ValueError) as error:
        print(f"oracle: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
