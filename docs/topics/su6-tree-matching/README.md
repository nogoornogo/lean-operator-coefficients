# SU(6) Exterior-Matter Tree Matching

- ID: su6-tree-matching
- Status: completed
- Result type: proved conditional algebraic matching.
- Working branch: `proof/su6-tree-matching`.
- Integration target: `master`.

## Frozen Endpoint

Test the existing algebraic SU(6) exterior-square 15, retaining the Q/up/e
states in the first-five-coordinate ten. Supply the explicit additional
adjoint background `D = v diag(2,2,2,-3,-3,0)` and the same paired quadratic
mass/action convention as the SU(5) pilot, with nonzero real g,v.

Derive the actual projected infinitesimal currents, including the five new
root pairs connecting the sixth coordinate to the first five. Check their
contribution rather than assuming spectator-current vanishing. Compute the
double-commutator masses of all eleven broken root pairs and verify that the
enumeration covers the nonzero mass entries. Use the generic exchange API
to obtain the full coefficient on the retained fields and test its nonzero
exterior descent against the original SU(5) result.

Two bounded routes: exterior-power compression/naturality for actual currents;
explicit diagonal mass algebra plus the existing spectator-inheritance API.
Stop if new group/representation or QFT foundations are needed. No arbitrary
SU(6) vacuum, full light spectrum, anomaly-free-model construction, full UV
Lagrangian, spinor reordering convention or decay amplitude is inferred.
This tests a concrete supplied bosonic background and an existing matter
representation, not every physical SU(6) theory.

## Interfaces And Acceptance

- [Actual SU(6) fifteen](../../../GUT/SU6/Representations/ConcreteSU6Representations.lean)
- [Standard-SM exterior branching](../../../GUT/SU6/Adapters/StandardSMExterior.lean)
- [Exterior action and tangent](../../../Math/RepresentationTheory/ExteriorSquareCoordinates.lean)
- [SU(5) actual currents](../../../GUT/SU5/Matching/HeavyCurrents.lean)
- [Generic mediator inheritance](../../../Math/LinearAlgebra/MediatorInheritance.lean)

Focused/full builds, strict transitive axiom audits, exact qque regressions,
layout/link/diff checks and merged-state rechecks. Lean LSP is unavailable.
No `sorry`, new axioms, dependency changes or heartbeat increases. Commit,
merge with `--no-ff` into master, retain branch and do not push.

## Results

The bounded experiment succeeds. The additional SU(6) channels are included
in the action, not discarded by an assumed no-cancellation condition.

| Derived quantity | Result |
| --- | --- |
| Six color/weak root pairs | Mass squared `25 g^2 v^2`; projected currents equal the actual SU(5) currents |
| Three color/sixth-coordinate pairs | Mass squared `4 g^2 v^2`; both retained-field currents zero |
| Two weak/sixth-coordinate pairs | Mass squared `9 g^2 v^2`; both retained-field currents zero |
| Full eleven-pair exchange | Exactly the SU(5) ordered qque coefficient |
| Intrinsic qque exterior sector | Equal to the SU(5) generated sector, hence nonzero |

The ordered scalar is `-g^2/(25 g^2 v^2) = -1/(25 v^2)` for nonzero
real g,v, in the existing paired-action convention. The scalar, ordered
functional and exterior sector are distinct objects; the result is not a
decay-width statement.

### Source Map

- [Exterior compression](../../../Math/RepresentationTheory/ExteriorSquareCompression.lean):
  a dimension-independent split inclusion/projection lemma for the actual
  exterior infinitesimal action. It does not assume the retained subspace
  is invariant under every generator.
- [Actual currents](../../../GUT/SU6/Matching/ExteriorCurrents.lean):
  identifies the exterior action with the existing algebraic SU(6) fifteen,
  embeds the ten into it, checks the standard-SM branching and quark
  covariance, and computes core and additional root currents. Zero means
  zero after projection to the retained targets, not zero action on the
  entire fifteen.
- [Adjoint masses](../../../GUT/SU6/Matching/AdjointMass.lean):
  trace-zero Hermitian background, eigenvalues for both orientations of
  every channel, positivity/invertibility, exhaustive coverage of unequal
  weight entries and vanishing on equal-weight entries.
- [Tree matching](../../../GUT/SU6/Matching/TreeMatching.lean):
  assembles the actual currents and diagonal mass on the eleven channels;
  `coefficient_eq` applies the generic spectator-inheritance theorem,
  `full_action_eq` identifies the eliminated quadratic action,
  `generated_eq` and `generated_nonzero` connect to the intrinsic qque sector.
- [Math audit](../../../Math/RepresentationTheory/Audit/AuditExteriorSquareCompression.lean)
  and [model audit](../../../GUT/SU6/Audit/AuditTreeMatching.lean):
  strict transitive audits of 2 and 31 declarations, respectively.

### Scope And Remaining Inputs

This closes a concrete larger-group application of structural inheritance.
It does not instantiate the no-shared-irreducible criterion of the
[representation-separated extension](../representation-separated-exchange/README.md):
here direct exterior-action calculations derive the support conditions.
It also supplies a reusable compression lemma without a new representation
or QFT foundation.

The chosen adjoint background and normalized paired quadratic action remain
explicit model choices. The background has unbroken, massless directions;
only the broken-root sector is inverted. The retained ten is selected, not
derived as a fermion mass radical. No potential selecting the background,
complete anomaly-free matter content, Yukawa sector, full UV Lagrangian,
arbitrary SU(6) vacuum, or physical on-shell amplitude is constructed.
No claim is made for other external fields, mediator sectors or backgrounds.

## Verification

- `lake build GUT.SU6.Matching.TreeMatching`: passed.
- `lake build Math.RepresentationTheory.Audit.AuditExteriorSquareCompression GUT.SU6.Audit.AuditTreeMatching`:
  passed; 33 strict checks allowing only `propext`, `Classical.choice`,
  `Quot.sound`, with no new axiom exceptions.
- `python3 tools/qque/audit_one_generation.py`: 4 tests passed.
- `python3 tools/qque/audit_pairwise.py`: 3 tests passed.
- `python3 tools/qque/audit_contraction_uniqueness.py`: 3 tests passed.
  These exact finite regression checks supplement, not replace, the Lean proofs.
- `node tools/layout/check-layout.mjs`: passed, 752 modules.
- Full `lake build`: passed, 5803 jobs. Existing warnings were replayed;
  new proof files have no warnings.
- `node tools/docs/check-links.mjs`: passed, 290 Markdown files,
  1705 local links, 33 heading fragments.
- `git diff --check`: passed.
- Repeat the full build, regressions, layout/link/diff checks after integration.
  Git ancestry records the topic/merge commits; retain the branch and do not push.

The frozen endpoint is complete. Further model backgrounds or additional
external sectors are separate tasks; no new physical premise has been
silently added to obtain the nonzero result.

The [post-SU(6) plan](../post-su6-generalization/README.md) prioritizes a
uniform exterior-matter family before variable diagonal backgrounds.
The later [uniform matching topic](../sun-variable-tree-matching/README.md)
implements the variable-background family directly and recovers this SU(6)
result. That extension is recorded separately from this verification.
