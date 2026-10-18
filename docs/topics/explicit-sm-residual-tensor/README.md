# Explicit SM x H QQue Tensor

- ID: explicit-sm-residual-tensor
- Status: completed
- Working branch: `proof/explicit-sm-residual-tensor`.
- Integration target: `master`.

## Frozen Endpoint

Construct a nonzero ordered SM x H invariant qque functional on explicitly
decomposed fields. Use the covering gauge group SU(3) x SU(2) x U(1) and the
existing quark/up-right/electron-right representations. Combine the checked
gauge tensor with an H-invariant multiplicity functional, then transport along
explicit SM x H representation equivalences. Connect to the compact light qque
source so its residual functional is derived, not an added existence premise.

The extra SM decomposition/equivariant field identifications are explicit
adapter inputs, NOT consequences of the old torus/index conditions. Q appears
twice as the same field representation. Right-handed up/electron slots use
contragredient multiplicities. When fields are subspaces of a left-chiral light
representation, right-handed fields belong to its dual, not the original space.

## Deliverables And Stop Gate

1. Reusable external tensor-product regrouping and nonzero invariant product.
2. Actual field-order SM x H qque functional, with a nonzero control and
   transport through explicit decompositions.
3. Adapter consuming the compact actual-light coefficient theorem; document
   exactly which new SM data are assumed.
4. Persistent strict axiom audits, full build, layout/link checks, commit/merge.

Stop at this ordered internal tensor. Do not develop Lorentz or Grassmann
algebras, assert generated interactions, derive arbitrary-radical SM extensions,
or change the E6 literature boundary. No dependency upgrades. A new required
physical assumption or foundational prerequisite triggers a scope review.

## Result

Proved, conditional on the explicit decomposition input. The algebraic
construction works for arbitrary H once a nonzero residual coefficient is
given. The compact source adapter derives that coefficient on the original
mass-radical weight spaces, then produces a nonzero SM x H functional on the
supplied actual Q subrepresentation and right-handed up/electron subspaces
of the dual radical. Compatibility with the original torus and H actions is
part of the new input; residual agreement is explicitly checked.

All four deliverables are complete. S3/A4 decomposed-field controls are
checked, as is preservation/reflection of coefficient nonvanishing. They are
not inhabitants of an ambient source with the additional decomposition.
The exact interfaces and remaining boundaries are in the
[proof dossier](../../proof/current/applications/Physics/EXPLICIT_SM_RESIDUAL_TENSOR.md).

No remaining work within this endpoint. Lorentz/Grassmann nonvanishing and
constructing full-SM decompositions for further sources are separate themes.

## Verification

stage 01:

- `lake build Math.RepresentationTheory.Audit.AuditExternalInvariantTensor Physics.StandardModel.Gauge.Audit.AuditExplicitSMResidualTensor`:
  passed, 3917 jobs; 8 mathematics and 11 physics transitive axiom checks.
- `lake build`: passed, 5652 jobs, including the aggregate modules.
- `node tools/layout/check-layout.mjs`: 615 modules; all checks passed.
- `node tools/docs/check-links.mjs`: 250 files, 1371 links, no errors.
- `git diff --check`: passed.

Only the standard `propext`, `Classical.choice`, `Quot.sound` axioms are
allowed. No placeholders, new axioms, audit exceptions or pin changes.
Inherited dependency/style warnings remain; new modules build without warnings.
Lean LSP MCP is unavailable; used source inspection and focused builds.

Integration target remains `master`; Git ancestry records the actual merge.

## Inputs

- [Existing SM gauge tensor](../../proof/current/applications/Physics/SM_GAUGE_TENSOR.md).
- [Compact actual-light coefficient](../../proof/current/applications/Physics/COMPACT_LIGHT_QQUE.md).
