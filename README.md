# hilbert-mathlib

Personal Mathlib for **David Hilbert** — shared background for formalizing old papers, plus paper-specific formalizations.

This is **not** a Mathlib fork, but a satellite library that `depends on Mathlib`.

## Structure

```
HilbertMathlib/
  Foundation/        — reusable background shared across all papers
    Basic.lean
  Foundation.lean    — re-exports Foundation
HilbertMathlib.lean  — root (personal mathlib)

Papers/
  Hilbert2021Convergence/  — first paper formalization (depends on HilbertMathlib + Mathlib)
    Basic.lean
  Hilbert2021Convergence.lean

blueprint/           — LaTeX blueprint (informal <-> formal correspondence)
```

## Build

```bash
lake update          # fetch mathlib (first time ~ few minutes)
lake build           # build entire project
lake build HilbertMathlib
lake build Papers.Hilbert2021Convergence
```

## Adding a new paper

1. Create `Papers/My2024Paper/` + `Papers/My2024Paper.lean` root
2. Add a `[[lean_lib]]` entry in `lakefile.toml` (copy the Hilbert2021Convergence block)
3. Import `HilbertMathlib` for shared background

## Reusing existing formalizations

* **Prefer `require`**: if a lemma lives in a maintained library, add it as `[[require]]` in `lakefile.toml` instead of copying.
* **Copy with attribution** (MIT/Apache-2.0 only): keep file header:
  ```lean
  -- Adapted from https://github.com/org/repo/blob/commit/File.lean, LICENSE, author
  ```

## License

MIT — see [LICENSE](LICENSE)
