# Delta-B Two Residual Selection Criteria

- ID: `delta-b-two-selection-criteria`
- Status: completed
- Result type: proved scalar and cyclic necessary-and-sufficient selection criteria
- Working branch: `proof/delta-b-two-selection-criteria`
- Integration target: `master`
- Integration evidence: master integration authorized at stage 01; Git ancestry records the merge

## Endpoint And Scope

Extend the completed residual-selection API to the independently defined
derivative-free six-right-quark degree `(2,4)` physical sector. Preserve the
typed up/down exchange constraints and existing finite-dimensional interface.
For one-generation cyclic charges prove allowance iff `2u + 4d = 0`,
prohibition iff the opposite condition, and a two-coordinate classification
in the neutral case. Transport the criteria to supplied actual fields.

Then combine this with the existing four-family Delta-B-one prohibition and
Weinberg allowance criteria. No arbitrary six-quark species/chirality census,
general-generation charge classification, anomaly claim or UV matching is added.

## Deliverables And Acceptance

- Proved scalar-character reduction with both converse witnesses and zero case.
- Cyclic charge iff and neutral-case physical two-coordinate equivalence.
- Actual-field transport preserving the supplied equivariant identifications.
- Simultaneous Delta-B-one / Delta-B-two / LLHH criteria and finite controls.
- Strict transitive audits, focused/full builds, layout/link/diff checks,
  proof dossier and verified assumptions entries.

See [the frozen plan](plan.md). A nontrivial scalar character must not be
silently treated as a trivial action on each individual field.

## Work And Open Obligations

All five milestones are complete. The degree-weighted residual action is proved
on typed ordered coefficients, then transferred through the existing equivalence
from the independent physical exterior sector. This avoids a new exterior-action
foundation while proving the same frozen physical endpoint. No implementation
obligation remains within this scope.

## Result And Verification

The [proof dossier](../../proof/current/applications/Physics/DELTA_B_TWO_SELECTION_CRITERIA.md)
records the arbitrary-group scalar criterion, both two-probe inverses,
literal pair equivalence, actual-field transport and cyclic simultaneous tests.
The existing general constrained-Hom interface is preserved. A neutral total
character, not trivial individual actions, is the exact scalar condition.

Z2 quark parity allows this six-quark sector while forbidding Delta-B-one;
Z5 `(1,1,0,0,0)` forbids both specified baryon sectors while allowing LLHH.
Trivial charges and order one allow the six-quark sector. No anomaly or Yukawa
compatibility interpretation is inferred.

Verification (stage 01):

- Focused builds of scalar/cyclic sources and
  `lake build Physics.StandardModel.Operators.Audit.AuditDeltaBTwoSelection`
  pass. The persistent audit has 29 strict transitive checks, permitting only
  `propext`, `Classical.choice`, `Quot.sound`.
- `lake build` succeeds (6,429 jobs), with no new warnings.
- `node tools/layout/check-layout.mjs` succeeds (1,102 modules).
- `node tools/docs/check-links.mjs`: 424 Markdown files, 2,853 links,
  zero errors. Docs/layout regression tests pass 14/14 (temporary-Git tests
  run outside the sandbox). `git diff --check` passes.

Dependency pins, root README, literature coverage and audit allowances are
unchanged. The user authorized closing and merging this topic at stage 01.
The verified proof checkpoint is `checkpoint 01`; Git ancestry is authoritative for
integration. The historical working branch is retained here after cleanup.

## References

- [Plan](plan.md)
- [Previous selection criteria](../residual-selection-criteria/README.md)
- [Six-quark interface](../delta-b-two-model-interface/README.md)
- [Physical bridge](../../../Physics/StandardModel/Operators/DeltaBTwoFlavorBridge.lean)
- [Common certificate](../../../Physics/StandardModel/Operators/ResidualSelectionCriteria.lean)
- [Cyclic character](../../../Math/RepresentationTheory/CyclicCharge.lean)
