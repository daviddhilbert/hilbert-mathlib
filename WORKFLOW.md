# Workflow for shared mathematical foundations

This repository owns reusable, paper-independent definitions and proofs.
The paper repositories consume its checked releases through Lake. Work on an
approved task continuously; routine implementation choices and reversible
checks do not require renewed permission.

## 1. Establish the scope and current state

Read README.md, CONTRIBUTING.md, AGENTS.md and any module-specific instructions.
Inspect Git status and preserve unrelated edits. Record the exact mathematical
statement, definitions, universes, parameter scope and hypotheses before
implementing or extracting a result. Distinguish proved results, explicit
reference hypotheses, adapters and unfinished obligations.

Use the repository's pinned Lean toolchain, Mathlib revision and Lake manifest.
Dependency upgrades are separate compatibility changes, not incidental fixes
to make a proof compile. The initial shared baseline is Lean 4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679.

## 2. Decide ownership before extraction

Put material here when its mathematical interface is independent of a paper
and its entire custom import closure belongs in this foundation. Generic
model theory, definable presentations, algebra, valuations, finite-coordinate
constructions and abstract Euler calculus can qualify. An ACVF-independent
import graph alone does not settle mathematical ownership.

Keep this Lake package dependent only on Mathlib and its inherited packages.
Do not introduce dependencies on ACVF-QE, special-transformations,
integration-in-ACVF, Fubini theorems or diamond-integral: those repositories
must be able to depend on this one without a cycle. Keep the common LRV
encoding and its specialized interfaces with their existing ACVF-QE owner
unless a separate reorganization is approved. Do not create competing copies.

Keep paper-specific constructions and numbered-result wrappers in their paper
repository. When a file mixes generic mathematics with a specialized adapter,
separate the generic declarations first and prove any required interface
correspondence. Similar names or mathematical roles do not establish equality
of two APIs, parameter conventions or hypotheses.

The author approved the November 16 cross-repository inventory of 106 shared
modules after reviewing ownership. SOURCE-MANIFEST.json records their exact
origins. Review ownership separately for additional extractions.

## 3. Survey reuse and preserve provenance

Search the pinned Mathlib, this library and the existing paper repositories
before building a substantial prerequisite. Inspect actual declarations and
hypotheses, not only filenames, citations or status counts.

For extracted or adapted sources, record the original repository, exact commit,
file and declaration names, license notices and changes made. Preserve original
copyright, attribution and applicable LICENSE/NOTICE files. In particular,
retain the existing notices on the Grothendieck-completion, ultrapower and
Newton-Puiseux adaptations. Do not replace an original source notice with the
repository's general MIT notice.

## 4. Implement a coherent shared module

Use a subject-based layout below HilbertMathlib/Foundation initially, with
small explicit imports. Preserve mathematical statements and public names
during an extraction; namespace changes and stronger generalizations are
separate changes. Add the module to an appropriate library entry point.

Move one coherent dependency-closed group at a time. Keep import-only
compatibility modules in the old repository when needed; a definition should
have one implementation owner. Preserve finite tags, zero cases, positivity,
noncommutative versus commutative scope and every mathematical hypothesis.
Do not assume cancellation or strengthen a conclusion to simplify an adapter.

Keep experiments and compiler output in .scratch/. Do not edit files during
the compiler run certifying those files.

## 5. Verify the source and interfaces

From a fresh checkout of the pinned project, run:

```sh
lake update
lake exe cache get
lake build HilbertMathlib
```

Run the actual affected module and relevant library entry points through Lake.
For every new or moved headline, compile a Lean audit containing its full type
and `#print axioms`. Accept only propext, Classical.choice and Quot.sound.
Inspect explicit theorem hypotheses as well: an allowed axiom list does not
discharge a mathematical premise. Reject proof placeholders, custom axioms
and theorems that merely assume their intended conclusion.

Record the exact source and dependency revisions, commands, exit status,
headline types, principles and relevant diagnostics. Cached results require
matching source and dependency fingerprints. Clearly distinguish fresh source
compilation, kernel replay, retained historical evidence and unverified drafts.

GitHub Actions checks the pinned library build, followed by
`python3 verification/verify.py`. This checks the source inventory and
fingerprints, compares all inventoried public signatures with the checked
pre-extraction baseline, and checks their exact principle inventories.
Extend the audit when adding mathematical declarations; update an expected
signature only after reviewing the full mathematical statement.

## 6. Check downstream consumers before retiring copies

For each extraction, identify every importing repository. Compile the original
and extracted headline types, then test the affected consumer at an exact
shared-library commit. Keep proven adapters when the representations differ.
Delete an old proof body only after its consumer builds and its headline audit
passes through the new provider. Preserve aliases needed by later sections.

The shared release comes first, followed by downstream pin updates in
dependency order. A working branch or a floating main dependency is not a
reproducible release. Check the relevant Fubini and diamond-integral entry
points when their prerequisite providers change. Preserve scoped lifting and
kernel adapters until a checked upstream interface actually replaces them.

## 7. Publish and report within the authorized scope

Review the diff and include only the requested change. Commit and push when
the user has authorized publication; do not infer authorization to migrate
proofs from a request to inspect dependencies or add workflow documentation.
Verify the remote revision and CI outcome. Report what was checked, remaining
explicit inputs and any consumer checks still pending. Green CI does not
replace mathematical statement review or establish untested downstream builds.
