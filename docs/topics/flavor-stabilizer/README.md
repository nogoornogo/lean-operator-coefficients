# Specified Flavor Stabilizers

- ID: `flavor-stabilizer`
- Status: completed
- Result type: bounded algebraic proof package
- Working branch: `proof/flavor-stabilizer`
- Integration target: `proof/vev-stabilizer`, not `master`.
- Parent exception: bounded child continuation of the unmerged specified-VEV
  topic, under the repository child-branch rule. Parent master merge authorized
  at stage 01; no push authorized.

## Frozen Endpoint

Construct the exact subgroup of a supplied candidate flavor group preserving
specified tensors/couplings and VEVs. Distinguish invariance of the full coupling
from invariance of its evaluated mass. Prove the evaluation inclusion and its
exact obstruction, with a generating-vacua criterion for recovering a coupling.
Supply the restricted representations and residual-Hom interface.

The initial classification pilot is one complex flavor line with its Circle
phase action and a symmetric Majorana form: zero coefficient has the full
Circle stabilizer; a nonzero coefficient has precisely the order-two roots.
Include zero-VEV accidental mass symmetry as a strictness regression. This is
not a classification of arbitrary simultaneous Yukawa matrices or a derivation
of nature's flavor group, couplings, vacuum or kinetic terms.

The finite diagonal continuation classifies all supports inside the supplied
independent-phase group, including an explicit Circle/sign product equivalence
and the exact condition for VEV evaluation to preserve the residual group.

The general algebraic interfaces allow arbitrary groups and module dimensions.
The existing finite-dimensional unitary-centralizer classification supplies a
candidate maximal mixing group when its hypotheses and decomposition model
are supplied; it is not automatically the symmetry of interacting couplings.
No diagonalization, numerical mass fitting, RGE, anomalies or dynamics is in scope.

## Plan And Acceptance

Continuation frozen at stage 01, resuming the retained child from parent
`checkpoint 01`: classify a finite diagonal Majorana form within the specified product
of independent Circle phases. Prove exact membership and a group equivalence
with Circle factors on zero coordinates and order-two factors elsewhere.
Verify zero/all-nonzero controls, VEV support loss and residual-Hom transport.
The candidate is not full U(n): rotations among equal or zero entries are out
of scope. No Takagi/SVD or simultaneous-matrix foundation is added.
The integration target remains the unmerged VEV parent.

1. General family-fixing subgroup and restriction/maximality interfaces.
2. Coupling/VEV preservation, evaluated-mass stabilizer and exact discrepancy;
   generating-vacua recovery without assuming finite dimension.
3. Circle/Majorana pilot, explicit roots/cyclic group equivalence and degeneration.
4. Residual invariant Hom and audit of the actual input conditions.
5. Focused/full builds, persistent strict transitive audit, layout/links/diff;
   commit verified milestones and merge the child only into its recorded parent.

Stop on a new foundational prerequisite or a change in physical scope. No
arbitrary-matrix orbit classification is silently added to this endpoint.

## Existing Sources

- [Unitary multiplicity centralizer](../../../Math/RepresentationTheory/Multiplicity/MultiplicityUnitaryCentralizer.lean)
- [Symmetric-form action](../../../Physics/FieldTheory/Yukawa/SymmetricScalarYukawa.lean)
- [Yukawa classification](../../../Physics/FieldTheory/Yukawa/YukawaClassification.lean)
- [Surjective Hom transport](../../../Math/RepresentationTheory/Decomposition/SurjectiveHomTransport.lean)
- [Parent VEV topic](../vev-stabilizer/README.md)

## Results

See [proved interfaces and boundaries](results.md): actual gauge-commuting
candidate action; arbitrary specified-family stabilizers; exact coupling/mass
evaluation obstruction; Yukawa-sector and residual-Hom connections; the
Circle-to-order-two Majorana pilot and a zero-VEV strictness control.
The finite diagonal continuation adds mixed-support product coordinates,
VEV support detection, and residual-Hom/nonzero transport.

## Verification

At creation the parent passed full `lake build` (6048 jobs) and 42 strict
stabilizer checks; that was the parent baseline, not child verification. Unrelated user changes
remain excluded from this topic's commits.

Final verification (stage 01):

- `lake build Physics.FieldTheory.Yukawa.Audit.AuditFlavorStabilizer`: passed,
  3768 jobs and 37 strict transitive checks; only `propext`, `Classical.choice`,
  `Quot.sound`. Intermediate elaboration errors were corrected; no failed
  build or generated error placeholder is treated as verification.
- Full `lake build`: passed, 6053 jobs, after the final general Hom signature
  update. No new-source warnings; existing dependency warnings replayed.
- `node tools/layout/check-layout.mjs`: passed, 1000 modules.
- Local links: 354 Markdown files, 2248 links, 34 fragments, zero errors.
  One later invocation hit an environment `spawnSync git EPERM`; a separate rerun passed.
  `git diff --check` passed.
- No dependencies, pins, audit exceptions, custom axioms or resource limits
  changed. Existing operator numerical/exact scripts were not rerun because
  their coefficient definitions and normalization conventions are unchanged.

Child integration is recorded by Git ancestry into `proof/vev-stabilizer`.
The child branch is retained. The parent was merged into master as `checkpoint 02`
at stage 01 following explicit user authorization.

- Proof commit: `checkpoint 03`; no-ff child merge into the parent: `checkpoint 04`.
- Merged-state full `lake build`: passed again, 6053 jobs. Layout, links and
  diff checks passed again. Existing dependency warnings replayed.
- This subsequent integration-record edit is documentation-only; no additional
  Lean build is rerun for it. No source changed after the merged-state build.

Diagonal continuation verification (stage 01):

- Focused audit build: passed, 3771 jobs and 54 strict transitive checks;
  permitted axioms remain only `propext`, `Classical.choice`, `Quot.sound`.
- Full `lake build`: passed, 6054 jobs. No new-source warnings; existing
  dependency warnings replayed. Intermediate elaboration errors were fixed.
- Layout: passed, 1001 modules. Links: 354 Markdown files, 2249 local links,
  34 fragments, zero errors. `git diff --check` passed.
- No pins, dependencies, resource limits or audit exceptions changed. Operator
  coefficient cross-check scripts are unaffected and were not rerun.
- Child resumed from `checkpoint 01`; subsequent parent master merge: `checkpoint 02`.
- Continuation proof commit: `checkpoint 05`; no-ff child merge into the parent:
  `checkpoint 06`. Merged-state full build passed again (6054 jobs), as did layout,
  local links and diff checks. The child branch remains retained.
- This integration-record-only edit does not rerun Lean; no proof changed
  after the merged-state verification.
