# Current Theorem Assumptions

This completed topic records its conjugation-input documentation checkpoint.
It is not a second live ledger; maintained inputs are in the
[layered assumptions index](../../proof/ASSUMPTIONS.md).

- ID: current-theorem-assumptions
- Status: completed
- Result type: documentation
- Working branch: `docs/current-theorem-assumptions`
- Integration target: `master`

## Goal And Stop Condition

Rewrite [the assumption ledger](../../proof/ASSUMPTIONS.md) against the current
two-conjugation Abelian and finite non-Abelian theorem signatures. Distinguish
inputs, derived properties, conclusions and older model-specific adapters.
Preserve the E6 literature boundary, physical scope and historical links.
Stop after source comparison, local-link validation and whitespace review.
No Lean changes, dependency changes, new theorem claims or full-build baseline.

## Source Comparison

- `TwoConjugationQque`: arbitrary Abelian H; torus x H unitarity;
  coefficientwise local dual target; Q-only slotwise and Q/down pair endpoints.
- `TwoConjugationLightQque`: finite H at constituent/coefficient extraction;
  torus-only unitarity; representation-valued local dual target.
- `InvariantMassData` / `SymmetricMassIndex`: invariant symmetric bilinear
  mass; radical preservation is derived via an intertwiner kernel.
- `ContinuousProfileModel`: retained SU(6) wrapper with stronger source inputs.

## Verification

Source comparison completed without changing any theorem. The new ledger
separates four endpoints, restricted unitarity requirements, local target
equations, derived light preservation/support, and older model adapters.
The existing `conditions-no-longer-required` anchor is retained.

- `node tools/docs/check-links.mjs`: 242 Markdown files, 1313 local links,
  32 heading fragments, zero errors.
- `git diff --check`: passed.
- No Lean build was rerun: this is documentation-only and does not establish
  a new proof verification baseline.

Integration follows the repository's `--no-ff` workflow; Git ancestry records
the actual merge. Retain the topic branch; no remote push.
