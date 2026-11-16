# Working instructions

- Read WORKFLOW.md, README.md and CONTRIBUTING.md before substantive work.
- This is a shared foundation, not a paper repository. It must not depend on
  ACVF-QE, special-transformations, integration-in-ACVF, Fubini theorems or
  diamond-integral. Preserve an acyclic package graph.
- Use the pinned Lean, Mathlib and Lake manifest. Preserve unrelated edits.
- Review mathematical ownership before moving modules. The current ownership
  proposal is not migration approval; the author requested that review first.
- Search existing libraries before rebuilding prerequisites. Preserve source
  commits, mathematical hypotheses, provenance and license notices.
- Require successful source compilation, full headline-type inspection and
  principle audits allowing only propext, Classical.choice and Quot.sound.
  A clean principle list does not discharge explicit theorem hypotheses.
- Validate affected downstream imports before retiring a duplicate proof body.
- Keep scratch work in .scratch/. Do not edit sources during their compiler run.
- Work persistently within the approved scope and avoid repeated permission
  requests for routine reversible work. Publish only within the user's
  authorization, and report the actual scope of verification.
