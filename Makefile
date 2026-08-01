UV ?= uv

# The oracle build is the shared resource here, and two of them at once would
# only duplicate work. Correctness does not depend on this: a build stages in a
# directory of its own and is published in one step.
.NOTPARALLEL:

.PHONY: help setup test oracle oracle-verify corpus lean go js check clean distclean

help:
	@echo "setup          install the Python environment"
	@echo "test           run the Python tests (builds the oracle if needed)"
	@echo "oracle         build the pinned pcre2 and the shim"
	@echo "oracle-verify  build it, then check it field by field against the pin"
	@echo "corpus         run the seed corpus against the oracle"
	@echo "lean           lake build"
	@echo "go             go vet and go test on the generated Go"
	@echo "js             node --test on the generated JavaScript"
	@echo "check          all of the above"
	@echo "clean          remove build trees, keep the downloaded tarball"
	@echo "distclean      remove the download cache too"

setup:
	$(UV) sync

test: setup
	$(UV) run pytest

oracle: setup
	$(UV) run python -m pcretruste.oracle build

oracle-verify: setup
	$(UV) run python -m pcretruste.oracle verify

corpus: setup
	$(UV) run python -m pcretruste.oracle corpus

lean:
	cd lean && lake build

go:
	cd gen/go && go vet ./... && go test ./...

js:
	cd gen/js && node --test

check: oracle-verify test lean go js

clean:
	rm -rf tmp/oracle/pcre2-* lean/.lake .pytest_cache
	find src tests -name __pycache__ -type d -prune -exec rm -rf {} +

distclean: clean
	rm -rf tmp/oracle .venv
