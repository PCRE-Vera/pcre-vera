UV ?= uv

# The oracle build is the shared resource here, and two of them at once would
# only duplicate work. Correctness does not depend on this: a build stages in a
# directory of its own and is published in one step.
.NOTPARALLEL:

.PHONY: help setup test oracle oracle-verify corpus generate generate-verify \
        sweep lean go js js-lint check clean distclean

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

lean:
	cd lean && lake build

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

clean:
	rm -rf tmp/oracle/pcre2-* lean/.lake .pytest_cache
	find src tests -name __pycache__ -type d -prune -exec rm -rf {} +

distclean: clean
	rm -rf tmp/oracle .venv gen/js/node_modules
