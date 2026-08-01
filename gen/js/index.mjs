// The JavaScript form of the pcre-truste engine: the module generated from the
// TIR artifact, plus the hand-written wrapper that gives it the API of
// DESIGN.md section 2.4.
//
// Nothing is generated yet. The printer lands in M4, together with the compile
// and match entry points; the analysis accessors and the preallocated match
// context follow in M5. Until then this module exists so that the toolchain,
// the package, and CI are in place, and so that the identity a generated module
// carries is fixed from the start: every generated file records the SHA-256 of
// the engine.tir.json it came from.

/** SHA-256 of the TIR artifact this module was generated from, empty until one is. */
export const artifactSha256 = "";

/** Whether this module holds a generated engine. */
export function generated() {
  return artifactSha256 !== "";
}
