# Full-SM Light-Source Bridge

- ID: `full-sm-light-bridge`.
- Status: completed
- Checkpoint detail: completed; compatible light-action connection theorem and audits checked.
- Result type: proved implication on the approved source inputs, not a new UV model.
- Working branch: `audit/full-sm-light-bridge`.
- Integration target: `master`; retain the branch. Git ancestry records integration.

## Endpoint And Scope

The requested first phase is a bounded design audit of a full-SM connection
for the actual mass radical. It is not a proof that the current four-weight
inputs already imply that connection. Review code, pinned dependencies and
primary literature before deciding on additional source hypotheses.

The eventual proposed consumer is `QqueSpinorExterior.exists_on_fields`:
produce actual light Q, up-right and electron-right subrepresentations with a
nonzero invariant qque coefficient surviving fourth-exterior-power descent.
Keep SM-cover x compact continuous H x SL(2,C) invariance and the existing
local algebraic scope. Do not claim a nonzero Wilson coefficient or amplitude.

The audit considered two routes once, without new foundations:

1. Reconstruct the old `CompactExplicitSMTensor.Decomposition` from a clean
   light spectrum with no contaminating SM irreducibles at selected weights.
2. Extract SM multiplicity spaces directly from the radical and bypass that
   particular decomposition interface. This is the recommended route.

## Result

The approved separated route proves compatible light actions, continuous
residual multiplicities, common split quotients from both index inputs, and
nonzero exterior qque on actual field subspaces inside K/K.dual. Concrete SM
irreducibility, evaluation-image equivalences and dual split embeddings are
derived, not source premises. See [implementation](implementation.md), the [design](design.md), and
[code/literature evidence](evidence.md). No dependency or trust-boundary change
was needed.

The revised additional source inputs are explicit:

- A compatible continuous full-SM x H action on the unchanged light radical.
  Preservation of the radical by an action on the original matter supplies
  it; invariance of the same mass is a separate sufficient constructor.
- SM-species-resolved residual chiral indices identifying the Q, up and
  electron multiplicities, not just their four torus-weight indices.

The four-weight target and two actual conjugations remain the route to
target-character compatibility. No common quotient, chosen splitting,
nonzero qque tensor or favorable exchange symmetry becomes a source input.

`LightSMSpeciesQque.exists_actual_alternation` retains an ordered qque
coefficient with nonzero alternating descent; `exists_actual_exterior`
packages the nonzero invariant functional on the fourth exterior power.

This is not advertised as a pure weakening of the old theorem: it replaces
an explicit decomposition input with a different, more source-oriented
package. Logical comparison and source examples require their own checks.

## Work And Stop Gate

Design deliverables are recorded. Implementation adds companion results
without changing the old checked endpoints, their assumptions or dependencies.

The subsequent discussion approved separating the compatible action on K
from one sufficient way of constructing it. The connection core must not
require full-SM invariance of the mass on E. Supply that invariance only as
a separate constructor; also allow preservation of the original radical.
Keep the species-index and four-weight source conditions explicit. The
stronger global spectrum wrapper remains separate, not a replacement input.
See [implementation](implementation.md) for the revised endpoint and checks.

The local connection endpoint is closed. The global full-SM character wrapper
(FSM-5), comparison of sufficient conditions, and an ambient source instance
satisfying both target packages are separate follow-ups, not claims here.
Do not start them automatically. Controls exercise actual-field transport
with one generation's Q/up/e sectors and an extra self-dual singlet sector.

Stop before adding assumptions beyond that package, treating an isotypic
space as a whole weight space, changing dependencies, or opening general
highest-weight/compact-group topology projects. The E6 literature boundary
is unchanged. Do not merge an incomplete proof as a completed connection.

## Verification

Source/API inspection and primary-literature checks were performed on
stage 01. LSP MCP was unavailable; focused Lean builds were used.

Final source verification: `lake build` passed (5675 jobs), the two new audits
passed 36 strict axiom checks, and the exact qque regression passed four tests.
Layout checks passed for 638 modules. See the implementation record for the
earlier checkpoint and the remaining physical boundaries.

At the design checkpoint, `node tools/docs/check-links.mjs` passed: 259 Markdown files, 1439 local
links, 33 heading fragments, zero errors. `git diff --check` passed.
No Lean build was rerun for that documentation-only checkpoint. See
[implementation](implementation.md) for the subsequent proof checks.

## References

- [Current assumptions](../../proof/ASSUMPTIONS.md).
- [Explicit SM adapter](../../proof/current/applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md).
- [Existing exterior endpoint](../../proof/current/applications/Physics/LORENTZ_EXTERIOR_QQUE.md).
- [Concrete full-group branching](../../proof/current/inputs/GUT/SM_BRANCHING.md).
- [Workflow and computational audit rules](../../architecture/WORKFLOW.md).
