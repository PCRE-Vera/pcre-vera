// Package pcretruste is the Go form of the pcre-truste engine: the code
// generated from the TIR artifact, plus the hand-written wrapper that gives it
// the API of DESIGN.md section 2.4.
//
// Nothing is generated yet. The printer lands in M4, together with the compile
// and match entry points; the analysis accessors and the preallocated match
// context follow in M5. Until then this package exists so that the toolchain,
// the build, and CI are in place, and so that the identity a generated package
// carries is fixed from the start: every generated file records the SHA-256 of
// the engine.tir.json it came from, and ArtifactSHA256 is that hash in a form
// a program can check.
package pcretruste

// ArtifactSHA256 is the SHA-256 of the TIR artifact this package was generated
// from. It is empty for as long as nothing has been generated.
const ArtifactSHA256 = ""

// Generated reports whether this package holds a generated engine.
func Generated() bool {
	return ArtifactSHA256 != ""
}
