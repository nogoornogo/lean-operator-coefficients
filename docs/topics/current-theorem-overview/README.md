# Current Theorem Overview

This is the completed full-SM-bridge documentation checkpoint, not a maintained
overview of subsequent results. The filename is retained for existing links;
use the [project README](../../../README.md) for the current selected claims.

- ID: current-theorem-overview
- Status: completed
- Result type: documentation.
- Working branch: `docs/current-theorem-overview`.
- Integration target: `master`.

## Endpoint

Synchronize the [public overview](../../../README.md) and the canonical
[assumptions ledger](../../proof/ASSUMPTIONS.md) with the completed
[full-SM light-source bridge](../full-sm-light-bridge/README.md).
Distinguish torus-only coefficients from actual SM/spinor/exterior coefficients,
and supplied-decomposition route A from species-index route B. Preserve the
stronger inputs of model-specific wrappers and the E6 literature boundary.

No new proof, dependency, license change, model realization or amplitude claim
is in scope. Stop after source-interface comparison, link/diff checks and merge.
Do not create a second root-level assumptions ledger.

## Result

The README now foregrounds the conditional compact non-Abelian actual-field
exterior result, separately from the retained model-specific selection rules.
The ledger distinguishes route A's supplied decompositions from route B's
continuous action on the original radical and species-index inputs. It names
derived outputs, states the actual exterior-functional conclusion, and retains
the non-dynamical and E6 boundaries. No Lean declarations or pins changed.

## Verification

- Compared the statements with `LightSMSpeciesQque`, `LightSMSpeciesIndex`,
  `LightSMAction`, `LightSMFieldExtraction` and `QqueSpinorExterior` sources.
- `node tools/docs/check-links.mjs`: 261 Markdown files, 1463 local inline
  links, 33 heading fragments, zero errors.
- `git diff --check`: passed.
- Lean builds and computational tests were not rerun for these prose-only
  changes. The owning proof topic retains its existing verification baseline.
- Integration target is `master`; Git ancestry records the completed merge.
