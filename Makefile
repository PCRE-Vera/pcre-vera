UV ?= uv

# The oracle build is the shared resource here, and two of them at once would
# only duplicate work. Correctness does not depend on this: a build stages in a
# directory of its own and is published in one step.
.NOTPARALLEL:

.PHONY: help setup test oracle oracle-verify corpus generate generate-verify \
        sweep lean go js js-lint check verify clean distclean

help:
	@echo "setup            install the Python environment"
	@echo "test             run the Python tests (builds the oracle if needed)"
	@echo "oracle           build the pinned pcre2 and the shim"
	@echo "oracle-verify    build it, then check it field by field against the pin"
	@echo "corpus           run the seed corpus against the oracle"
	@echo "generate         write the artifact, both backends, and the corpora"
	@echo "generate-verify  fail if any committed generated file has drifted"
	@echo "sweep            run the full differential sweep against pcre2"
	@echo "lean             lake build"
	@echo "go               go vet and go test on the generated Go"
	@echo "js               node --test on the generated JavaScript"
	@echo "js-lint          eslint on the generated JavaScript (needs npm)"
	@echo "check            all of the above"
	@echo "verify           the generated files, the freeze record, and the proofs"
	@echo "clean            remove build trees, keep the downloaded tarball"
	@echo "distclean        remove the download cache too"

setup:
	$(UV) sync

test: setup
	$(UV) run pytest

oracle: setup
	$(UV) run python -m pcrevera.oracle build

oracle-verify: setup
	$(UV) run python -m pcrevera.oracle verify

corpus: setup
	$(UV) run python -m pcrevera.oracle corpus

generate: setup
	$(UV) run python -m pcrevera.backends build

generate-verify: setup
	$(UV) run python -m pcrevera.backends verify

# The campaign of DESIGN.md section 8, which is minutes rather than seconds and
# so is not part of `check`: the committed shard under conformance/ is what
# runs on every commit. SWEEP holds whatever a run wants to change — a seed, a
# population size, an output directory.
SWEEP ?= --jobs 8

sweep: setup
	$(UV) run python -m pcrevera.sweep run $(SWEEP)

# Build the library and the proofs, then replay the conformance corpora
# through the Lean reference engine (DESIGN.md section 9, M6's R-10): the
# committed AST bridge feeds it the parsed trees, and any disagreement in
# outcome, ovector or usage fails the build.
lean:
	cd lean && lake build && lake exe corpuscheck \
	    ../conformance/corpus.json ../conformance/sweep.json \
	    ../gen/lean/bridge.json

go:
	cd gen/go && go vet ./... && go test ./...

js:
	cd gen/js && node --test

# The one thing here that wants the npm registry, and only when the lockfile
# moves: this is a file target rather than a phony one, so a bumped lockfile
# reinstalls and an unchanged one does nothing.
gen/js/node_modules: gen/js/package-lock.json
	cd gen/js && npm ci
	touch $@

js-lint: gen/js/node_modules
	cd gen/js && npm run --silent lint

check: oracle-verify generate-verify test lean go js js-lint

# M7's gate. It fails on: the artifact or another generated file drifting from
# the generator, a hash drifting from the freeze record, the coverage ledger
# drifting from the call graph, the artifact failing to decode inside Lean or
# to print back to its own bytes, and a broken proof.
#
# The two Artifact build products are removed first on purpose. `include_str`
# embeds the artifact at elaboration time, but lake does not know that file is
# an input, so a changed artifact with an unchanged `.lean` would be answered
# from a stale `.olean` — the check would pass without having run. Deleting
# them costs one module's elaboration and buys the guarantee.
#
# What it still does not do is bind the *proofs* to the artifact: the decode
# and the round trip say the bytes are the program the Lean side names, and
# the simulation lemmas that would say the program means what layer R means
# are gate 5's, and are not written.
verify: generate-verify
	$(UV) run pytest tests/test_freeze.py tests/test_coverage.py \
	    tests/test_strata.py tests/test_lean_pin.py
	rm -f lean/.lake/build/lib/lean/Pcrevera/Tir/Artifact.olean \
	      lean/.lake/build/lib/lean/Pcrevera/Tir/Artifact.trace
	$(MAKE) lean

clean:
	rm -rf tmp/oracle/pcre2-* lean/.lake .pytest_cache
	find src tests -name __pycache__ -type d -prune -exec rm -rf {} +

distclean: clean
	rm -rf tmp/oracle .venv gen/js/node_modules
