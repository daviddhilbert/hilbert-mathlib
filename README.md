# hilbert-mathlib

Personal Mathlib — shared, paper-independent background for formalizing mathematics.

This repository is **foundation only**. Paper-specific formalizations live in their own repositories and depend on this one through Lake.

## Structure

```
HilbertMathlib/
  Foundation/        — reusable definitions and lemmas shared across papers
    Basic.lean
  Foundation.lean    — re-exports Foundation
HilbertMathlib.lean  — root of the personal mathlib
```

## Build

```bash
lake update          # fetch Mathlib (first time only)
lake build
```

The shared baseline is Lean 4.35.0 with Mathlib pinned at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The Lake manifest records the
transitive dependency revisions. [Lean build](.github/workflows/lean.yml)
checks the library on pushes, pull requests and manual runs, saving compiled
files after the build.

See [WORKFLOW.md](WORKFLOW.md) for proof checks, module ownership and downstream
migration rules. No mathematical modules have been extracted into the current
foundation skeleton.

## Using from a paper repository

In the paper's `lakefile.toml`:

```toml
[[require]]
name = "hilbert-mathlib"
git = "https://github.com/daviddhilbert/hilbert-mathlib.git"
rev = "main"
```

Then `import HilbertMathlib` in the paper's Lean files.

## Adding shared material

Put it under `HilbertMathlib/Foundation/` only if it is independent of any particular paper. Paper-specific definitions and theorems belong in the paper repository.

## Reusing existing formalizations

* Prefer adding a `[[require]]` dependency over copying.
* If copying, check the source license and keep an attribution header:
  ```lean
  -- Adapted from https://github.com/org/repo/blob/<commit>/File.lean, MIT, author
  ```

## License

MIT — see [LICENSE](LICENSE)
