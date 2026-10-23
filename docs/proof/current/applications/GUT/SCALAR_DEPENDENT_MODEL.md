# Scalar-dependent SU(6) model endpoint

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Status: **LEAN-CHECKED**, MASS-3 (stage 01). The adapter, legacy recovery,
nonlinear benchmark, and zero-VEV controls pass audits and full regression.
See the [extension plan](../../../../topics/mass-profile-foundations/plans/MASS_AND_FLAVOR_EXTENSION_PLAN.md).

The subsequent [profile endpoint](PROFILE_MODEL.md) also removes the
single-charge-per-species target for positive generation totals.
`ContinuousProfileModel.ScalarModel` combines both extensions; the fixed-charge
dual-index model below, with a nonzero integer generation parameter, remains
available unchanged.

## 2. Inputs and conclusion

### Inputs and Conclusion

[ContinuousWeylFamilyModel](../../../../../GUT/SU6/SelectionRules/Models/ContinuousWeylFamilyModel.lean)
retains the existing continuous embedding geometry, canonical nonnegative
SU(6) matter source, ordinary Abelian residual group, nonzero generation
index, charges, and exact dual light-index target. Its primitive mass-sector
data are an actual finite-dimensional unitary scalar representation, an
invariant bare mass, an equivariant scalar-dependent symmetric bilinear
coefficient, and a vacuum fixed by the declared group. The coefficient is
jointly continuous in the scalar and both fermion variables; scalar-linearity
is not required. These are explicit model hypotheses, not conclusions about
an arbitrary Lagrangian.

`sector.mass` derives the invariant mass. `toMassModel` passes it to the
unchanged continuous symmetric-mass endpoint. The model therefore inherits
the standard hypercharge result, neutral proton charge functionals, and the
supported operator-signature obstruction for positive generation index.
For a nonzero signed index, the existing two-orientation conclusion remains
available. Finite Abelian residual groups require no altered argument.

The exact light target remains an applicability hypothesis. It is not
inferred from arbitrary coefficients or from their continuity. Support is
obtained through the actual radical of the derived mass, not from a signed
character alone.

## 4. Proof structure

### Verified Benchmark

[WeylMassFamilyBenchmark](../../../../../GUT/SU6/SelectionRules/Benchmarks/WeylMassFamilyBenchmark.lean)
recovers `ContinuousWeylFullMass.model` by a neutral quadratic
scalar, zero bare mass, and VEV one. The proved checks include a nonzero
mass, genuinely nonlinear coefficient, the exact 15-mode SM radical and
light spectrum, actual supported signature, and a zero-VEV control with
the same nonzero coefficient and whole-space radical.

The [model audit](../../../../../GUT/SU6/SelectionRules/Audit/AuditWeylMassFamilyModel.lean)
checks legacy equality and finite Abelian specialization. The generic
[source audit](../../../../../Physics/FieldTheory/Yukawa/Mass/Audit/AuditMultilinearWeylMass.lean)
retains a transitive SU(5)/SU(6)-free import guard for the power construction.

## 5. Lean entry points

### Source and Compatibility Bridges

The [finite-source API](../../inputs/Physics/SCALAR_DEPENDENT_MASS.md) constructs admissible
families and their joint continuity from covariant finite multilinear
coefficients and real-linear slots. Finite sums of such terms can be placed
in the model sector; conjugate slots are not called holomorphic. The model
also permits other jointly continuous equivariant families; polynomiality
is not a premise used by the downstream mass/index theorem.

`Model.ofLinearModel` converts every old `ContinuousWeylYukawaModel.Model`
without a new continuity hypothesis: finite-dimensional multilinearity
proves that condition. The entire `toMassModel`, the mass, and the actual
light spectrum are preserved by equality. No old theorem is replaced.

[WeylMassPolynomial](../../../../../Physics/FieldTheory/Yukawa/Mass/WeylMassPolynomial.lean) constructs
the neutral finite coefficient `C(s_1,...,s_n) = product(s_i) B` for any
invariant symmetric mass `B`. Its diagonal is `s^n B`. Zero bare mass and
VEV one recover `B` exactly, including at n=0; positive arity at VEV zero
instead gives zero mass. A nonzero `B` gives genuinely nonadditive scalar
dependence at n=2. Joint continuity follows from the MASS-2 theorem.
`Model.ofMassAsPower` consequently preserves an entire pre-existing mass
model, not merely its virtual index.

## 6. Scope and limitations

### Scope Boundary

`CombinedGroup H` here is `CompactTorus x H`, the existing physical-character
interface. Its scalar action is unitary; the model does not add a topology
or group-action continuity assumption on arbitrary `H`. Continuous geometry
and joint coefficient continuity are distinct hypotheses.

The power realization is an unbroken-interface compatibility example. It
does not upgrade the old torus-eigenbasis benchmark to full non-Abelian SM
invariance or produce new full-SU(6) scalar geometry. The separate full-gauge
mass/tensor and UV Yukawa realizations remain unchanged. No preferred VEV,
scalar potential, exact SM stabilizer, Lorentz/Grassmann nonvanishing, Wilson
coefficient, or decay amplitude is claimed. This closes only the planned
symmetric-mass source extension; nonlinear Dirac wrappers are deferred.

Declarations, reproducible commands, and the verification record are in the
[formalization dossier](interfaces/scalar-dependent-model.md).

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
