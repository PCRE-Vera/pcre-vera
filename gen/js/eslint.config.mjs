// The lint pass DESIGN.md section 9 asks M4 for. It runs over the hand-written
// wrapper and over the generated module alike: a printer that reached for a
// global it never defined should be told so here rather than at the first call.
//
// The generated files get a narrower rule set, and the reason is worth writing
// down. A printer emits one runtime helper per TIR operator whether or not the
// program it is printing uses that operator, and it emits a TIR `let` as a
// mutable slot whether or not this particular program writes to it twice.
// Neither is a defect, so `prefer-const` and the unused-helper complaint are
// turned off there; `no-undef`, which catches the thing that would actually
// break, stays on everywhere.

import js from "@eslint/js";

export default [
  js.configs.recommended,
  {
    languageOptions: {
      ecmaVersion: 2024,
      sourceType: "module",
    },
    linterOptions: {
      reportUnusedDisableDirectives: true,
    },
  },
  {
    files: ["index.mjs"],
    rules: {
      eqeqeq: ["error", "always"],
      "no-var": "error",
      "prefer-const": "error",
    },
  },
  {
    files: ["test/**/*.mjs"],
    languageOptions: {
      globals: { TextDecoder: "readonly", TextEncoder: "readonly", URL: "readonly" },
    },
  },
  {
    files: ["engine.mjs", "probe.mjs"],
    rules: {
      "no-unused-vars": "off",
      "no-useless-assignment": "off",
      "prefer-const": "off",
    },
  },
];
