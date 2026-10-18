# Qque Entry-Point Documentation Cleanup

- ID: `qque-entrypoint-docs`
- Status: completed
- Result type: documentation
- Working branch: `docs/qque-entrypoint-docs`
- Integration target: `master`
- Integration evidence: Git ancestry into `master`; documentation checks passed

## Endpoint And Scope

Reorganize the public README presentation of the qque results so that users
first see the practical entry points: complete classification/prohibition
criteria, equivalent constituent inspection, and the two main existence
packages from exact or vectorlike spectra. Preserve the detailed structural
endpoint inventory and point specialist APIs there instead of presenting every
intermediate sufficient condition as a peer entrance.

This is prose-only documentation. No Lean theorem, dependency pin, physical
scope, amplitude claim or proof baseline changes are in scope.

## Deliverables And Acceptance

- Update the root [README](../../../README.md) main-results section around qque
  entry points.
- Keep specialist routes linked, including route A/B, signed virtual-index,
  shared-positive, pairwise-positive, automatic species-index and balanced
  extension APIs.
- Add this topic record and index it from [topics](../README.md).
- Check local links and whitespace; explicitly skip Lean builds as prose-only.

## Work And Open Obligations

No open obligations remain for the scoped documentation update.

## Result And Verification

The root README now presents qque entry points by caller goal. It distinguishes
complete classification/prohibition APIs from sufficient existence packages,
keeps `QqueCommonIrreducible` visible as the readable equivalent criterion,
and moves route A/B plus signed virtual/shared/pairwise/automatic/balanced
APIs into the specialist structural layer. The assumptions ledger remains the
canonical detailed theorem table and was not changed.

Verification:

- `node tools/docs/check-links.mjs`: 284 Markdown files, 1639 local inline
  links, 33 heading fragments, 0 errors.
- `git diff --check`: passed.
- Lean builds and computational tests were not rerun; this is documentation-only
  and does not establish a new proof verification baseline.

## References

- [Full light-species topic](../qque-full-species-boundary/README.md)
- [Common-irreducible topic](../qque-common-irreducible/README.md)
- [Exact-spectrum entry](../exact-sm-spectrum-qque/results.md)
- [Vectorlike spectrum proof note](../../proof/current/inputs/Physics/VECTORLIKE_SPECTRUM.md)
- [Balanced species extension](../../proof/current/applications/Physics/BALANCED_SPECIES_EXTENSION.md)
- [Assumptions ledger](../../proof/ASSUMPTIONS.md)
