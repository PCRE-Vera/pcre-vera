// Package corpustest reads a conformance corpus, for the runners that check
// one.
//
// The envelope — the schema number and what a well-formed document looks like —
// lives in one place on the Python side (src/pcretruste/oracle/conformance.py)
// for the reason its docstring gives: the runners check one schema against
// every corpus and would otherwise each have to be told which is which. This is
// that one place on the Go side.
//
// It is a package of its own rather than a helper in a test file because the
// certificate runner has to live inside the generated engine package, where a
// helper next to the wrapper's tests cannot be seen. Nothing here takes a
// *testing.T, so the package does not drag the testing flags into the library.
package corpustest

import (
	"encoding/json"
	"fmt"
	"os"
)

// Schema is the envelope version every committed corpus carries.
const Schema = 1

// Read decodes the cases of one corpus, checking the envelope first.
func Read[T any](path string) ([]T, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var document struct {
		Schema int             `json:"schema"`
		Cases  json.RawMessage `json:"cases"`
	}
	if err := json.Unmarshal(raw, &document); err != nil {
		return nil, err
	}
	if document.Schema != Schema {
		return nil, fmt.Errorf("%s has schema %d, want %d", path, document.Schema, Schema)
	}
	var cases []T
	if err := json.Unmarshal(document.Cases, &cases); err != nil {
		return nil, err
	}
	if len(cases) == 0 {
		return nil, fmt.Errorf("%s holds no cases", path)
	}
	return cases, nil
}
