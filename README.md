# hilbert-mathlib

Personal Mathlib — shared, paper-independent background for formalizing mathematics.

This repository is **foundation only**. Paper-specific formalizations live in their own repositories and depend on this one through Lake.

## Structure

```
HilbertMathlib/
  Foundation/        — reusable definitions and lemmas shared across papers
    ModelTheory/      — elementary maps and model-theoretic constructions
    Definability/     — arbitrary-language definable spaces and maps
    Grothendieck/      — positive presentations and group completion
    Grading/          — gradings and localization
    Algebra/          — tensors and quotient constructions
    FiniteCoordinates/ — integer monomials and finite coordinates
    Euler/            — finite-jump functions and ordered Euler calculus
    Coaction/         — polynomial coactions and graded maps
    Series/           — Hahn, Laurent, Puiseux and Kummer algebra
    Order/            — finite-order controllers, cells and germs
    FieldTheory/      — transcendence degree and Krull dimension
    Polyhedra/        — rational polyhedra, triangulations, lattice-point series
    CategoryTheory/   — strict symmetric monoidal and Markov categories
    (also AlgebraicGeometry/, Valuation/, Topology/, FiniteSets/, Quotients/, Rewriting/)
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
files after the build. It then runs `python3 verification/verify.py`, comparing
the 3,153 inventoried public declarations with their pre-extraction full types
and principle inventories. Audit evidence is uploaded with each run.

See [WORKFLOW.md](WORKFLOW.md) for proof checks, module ownership and downstream
migration rules. The first extraction contains the 106 modules approved in
the November 16 ownership review. [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json)
records their exact source commits, original paths, source fingerprints and
new providers. Public declaration namespaces remain unchanged.

## Using from a paper repository

In the paper's `lakefile.toml`:

```toml
[[require]]
name = "hilbert-mathlib"
git = "https://github.com/daviddhilbert/hilbert-mathlib.git"
rev = "<checked hilbert-mathlib commit>"
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

The repository's original material is MIT — see [LICENSE](LICENSE).
Extracted files retain their original notices and applicable licenses.
The Grothendieck-ring and Newton–Puiseux adaptations are Apache 2.0;
their license texts and the ACVF-QE source license are retained under
[verification/third-party](verification/third-party). So are the Apache 2.0
licenses of diamond-integral, integration-in-ACVF and free-markov, and the
license and notice of Elliot Glazer's definable-saturated, from which
`ModelTheory/CountableSaturatedExtension.lean` is adapted.

The approved November 17 extraction adds generic mathematics from126 source files
(125 whole files and the generic core of one mixed file). Together with the
initial106 modules,232 modules retain their original public names and hypotheses.
The two paper relation wrappers in the mixed file remain in Fubini-theorems.
New families include field theory, valuations, algebraic geometry, topology,
quotients and rewriting; the package still depends only on Mathlib.

The November 22 extraction (batch `2026-11-22-tier1`) adds 149 modules from
ACVF-QE, Fubini-theorems, diamond-integral, integration-in-ACVF,
special-transformations and free-markov: 148 whole files and the generic core
of `ACVF-QE/Proofs/MarkerBridge.lean`. Public names, namespaces and hypotheses
are unchanged; each moved declaration's full type and axioms were compared with
the original, compiled in its source repository. New families: finite-order
controllers, Grothendieck-completion functoriality, definable families and named
maps, torus characters, Euler germs, graded actions and scalar extension,
transcendence degree and Krull dimension, rational polyhedra and lattice-point
series, definable Ax–Grothendieck, ACF quantifier elimination, countable
saturation and the saturated-model QE criterion, the Grothendieck ring of
ACF-definable sets, and strict symmetric monoidal and Markov categories. The
source repositories still hold their own copies until their consumers are
migrated.

The November 23 extraction (batch `2026-11-23-tier2`) adds 60 modules: laminar
set families, uniform finiteness formulas and elementary restriction of
definable maps, coordinate derivations, implicit Jacobians, Gauss valuations and
limit-polynomial roots, the one-sorted language of valued fields with its prime
models, amalgamation of valued fields with Chevalley's lemma, and the zero-degree
part of polynomial coactions. Four modules are generic cores split from mixed
files (`JohnsonLanguagePrime` without the ACVF theory, `JohnsonAmalgamation`'s
`Johnson22` namespace, and two blocks of diamond-integral section 4); one
module's unused paper import was replaced by Mathlib imports. The same
signature and axiom comparison with the original sources applies.
