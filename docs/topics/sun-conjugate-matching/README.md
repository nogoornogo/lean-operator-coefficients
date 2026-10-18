# Conjugate Embeddings And Matching Transport

- ID: sun-conjugate-matching
- Status: completed
- Result type: proved conditional transport and conjugate-embedding matching.
- Working branch: `proof/sun-conjugate-matching`.
- Integration target: `master`.

## Frozen Endpoint

Implement the third-stage compatible basis/embedding change. For the checked
variable diagonal SU(5+r) family, simultaneously conjugate the background,
root directions, group embedding and retained matter by a supplied SU(5+r)
element. Derive the new projected currents from the actual exterior action
and prove the new double-commutator eigenvalue identities. Transfer the
nonzero qque sector, with no equality/nonzero coefficient premise.

Also allow an arbitrary linear equivalence of the massive mediator carrier,
transporting the mass, source and dual current together. Prove preservation
of the full quadratic action and ordered/exterior coefficient. This may
produce non-diagonal coordinate masses but is not new dynamical mass mixing.

Routes: general algebraic transport of paired exchange; naturality of exterior
action and covariance of double commutators under matrix conjugation.
Check identity/composition and a control showing why the dual current must
also transform. Stop at these routes if new foundations are required.
Do not assert that arbitrary inequivalent embeddings, arbitrary split maps
or independently changed mass operators satisfy the compatibility conditions.
Do not add a vacuum, light-radical selection, amplitude or width claim.

## Interfaces

- [Previous family](../sun-variable-tree-matching/README.md)
- [Actual matter](../../../GUT/SUN/Matching/ExteriorMatter.lean)
- [Actual currents](../../../GUT/SUN/Matching/ExteriorCurrents.lean)
- [Matching](../../../GUT/SUN/Matching/TreeMatching.lean)
- [Exchange](../../../Math/LinearAlgebra/MediatorExchange.lean)
- [Exterior compression](../../../Math/RepresentationTheory/ExteriorSquareCompression.lean)
- [Qque inheritance](../../../Physics/StandardModel/Operators/QqueMediatorInheritance.lean)

## Acceptance

Focused/full builds, persistent strict transitive axiom audits, exact existing
qque regressions, layout/link/diff checks, commit and no-ff merge into master,
merged-state checks, retained branch, no push. No sorry, new axioms, dependency
or heartbeat changes. Lean LSP is unavailable; use targeted builds.

## Results

The frozen routes succeed. The result removes the first-five-coordinate and
diagonal-coordinate dependence of the checked construction under compatible
transport; it does not construct new gauge-inequivalent models.

### Generic Transport

[MediatorTransport](../../../Math/LinearAlgebra/MediatorTransport.lean)
constructs, for any linear equivalence T of the massive mediator carrier,
the mass T M T^-1, source T J and dual current K composed with T^-1.
It proves equality of the full quadratic action before elimination and of
the ordered exchange coefficient after elimination. Identity/composition
laws are checked. The dual transformation is essential: a rational control
shows that transforming only the source changes the exchange.

[ExteriorSquareTransport](../../../Math/RepresentationTheory/ExteriorSquareTransport.lean)
proves naturality of the actual infinitesimal exterior action under similarity
and covariance of double commutators. These are finite-dimensional matrix
and exterior-power statements, independent of particle labels.

[QqueMediatorTransport](../../../Physics/StandardModel/Operators/QqueMediatorTransport.lean)
derives invariant internal and generated exterior-sector preservation from
the exchange identity. Nonzero descent is not inferred merely from a
nonzero ordered tensor; the actual sector elements are equal.

### Actual Conjugated Family

For a supplied U in SU(5+r), [ConjugatedMatter](../../../GUT/SUN/Matching/ConjugatedMatter.lean)
constructs:

- B' = U B U^-1 and rotated root directions U X U^-1.
- The injective conjugated SU(5) embedding and retained matter inclusion
  exterior(U) composed with the old inclusion, with its compatible projection.
- The actual projected exterior currents, recomputed on these data.

It proves Hermiticity and trace zero of B', intertwining of the retained
group action, preservation of the split projection/inclusion, equality of
the two projected currents, and the rotated root mass eigenvalue equations.
`mass_zero_iff` preserves the full mass kernel under conjugation, not just
the displayed nonzero eigenvalues. Massless directions are still not inverted.

[ConjugatedMatching](../../../GUT/SUN/Matching/ConjugatedMatching.lean)
assembles those recomputed currents and permits a further arbitrary mediator
linear equivalence T. The reference mass in rotated-root coordinates is
justified by the proved eigenvalue equations, then transported by T.
`coefficient_eq`, `generated_eq` and `generated_nonzero` recover the old
family's ordered coefficient and nonzero intrinsic qque sector.
`action_eq` compares the full paired actions; `full_action_eq` retains
the ordered scalar -1/(a-b)^2 after elimination.

The equality compares coefficients using the transported identifications of
the retained external fields. It is not invariance of fixed ambient field
components while only the background changes.

### Controls And Limits

[ConjugatedControls](../../../GUT/SUN/Matching/ConjugatedControls.lean)
checks identity and composition of ambient rotations, conjugated backgrounds
and group embeddings, and recovers the SU(7) variable-spectator family for
every supplied U. The Math shear control turns diag(1,2) into a non-diagonal
coordinate mass: its value on (0,1) is (1,2). Such coordinate mixing is allowed.

This is not a theorem for independently changed mass mixing. All transported
objects must move together. An arbitrary mediator T preserves the algebraic
paired action; it need not preserve Hermiticity relative to an unchanged
standard inner product. The ambient U is genuinely unitary.

No claim is made that all embeddings or arbitrary split maps are conjugate
to the checked inclusion, or that any given non-diagonal background has the
required compatible retained fields. No spectral classification, new vacuum,
light-radical identification, full UV completion, amplitude or width is added.
Those remain independent tasks, not implicit premises proved by transport.

## Verification

- Focused `lake build GUT.SUN.Matching.ConjugatedControls`: passed.
- Focused strict audit build: `Math.LinearAlgebra.Audit.AuditMediatorTransport`,
  `Math.RepresentationTheory.Audit.AuditExteriorSquareTransport`,
  `Physics.StandardModel.Operators.Audit.AuditQqueMediatorTransport`,
  `GUT.SUN.Audit.AuditConjugatedMatching`: passed, 13+7+3+30 = 53 checks.
  Only `propext`, `Classical.choice`, `Quot.sound` are allowed.
- Exact regressions passed: `python3 tools/qque/audit_one_generation.py` (4),
  `python3 tools/qque/audit_pairwise.py` (3),
  `python3 tools/qque/audit_contraction_uniqueness.py` (3).
  The new identity/composition and rational controls are Lean proofs.
- `node tools/layout/check-layout.mjs`: passed, 770 modules.
- Full `lake build`: passed, 5821 jobs. Existing warnings were replayed;
  new proof files have no warnings.
- `node tools/docs/check-links.mjs`: passed, 293 Markdown files,
  1753 local inline links, 33 heading fragments.
- `git diff --check`: passed.
- No existing proof, dependency pin, heartbeat limit or axiom policy changed.
  Repeat the full build, regressions and layout/link/diff checks after merge.
  Git ancestry records topic/merge commits; retain branch, no push.

Stop here: both frozen transport routes and their controls are complete.
Independent mass mixing and inequivalent embeddings require new model data
and are not included by describing a coordinate change as a physical extension.
