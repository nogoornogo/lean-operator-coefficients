import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaCertificate
import Physics.FieldTheory.Mass.FlavorMajoranaUnitary
import Math.LinearAlgebra.UnitaryCongruenceCertificate
import Math.LinearAlgebra.TakagiExistence
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Flavor.FlavorMajoranaCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavorMajoranaCertificate.Input => Physics.FlavorMajoranaCertificate.Input,
  GUT.FlavorMajoranaCertificate.Input.basis => Physics.FlavorMajoranaCertificate.Input.basis,
  GUT.FlavorMajoranaCertificate.Input.casesOn => Physics.FlavorMajoranaCertificate.Input.casesOn,
  GUT.FlavorMajoranaCertificate.Input.ctorIdx => Physics.FlavorMajoranaCertificate.Input.ctorIdx,
  GUT.FlavorMajoranaCertificate.Input.mass => Physics.FlavorMajoranaCertificate.Input.mass,
  GUT.FlavorMajoranaCertificate.Input.matrix => Physics.FlavorMajoranaCertificate.Input.matrix,
  GUT.FlavorMajoranaCertificate.Input.mk => Physics.FlavorMajoranaCertificate.Input.mk,
  GUT.FlavorMajoranaCertificate.Input.mk.inj => Physics.FlavorMajoranaCertificate.Input.mk.inj,
  GUT.FlavorMajoranaCertificate.Input.mk.injEq => Physics.FlavorMajoranaCertificate.Input.mk.injEq,
  GUT.FlavorMajoranaCertificate.Input.mk.noConfusion => Physics.FlavorMajoranaCertificate.Input.mk.noConfusion,
  GUT.FlavorMajoranaCertificate.Input.mk.sizeOf_spec => Physics.FlavorMajoranaCertificate.Input.mk.sizeOf_spec,
  GUT.FlavorMajoranaCertificate.Input.noConfusion => Physics.FlavorMajoranaCertificate.Input.noConfusion,
  GUT.FlavorMajoranaCertificate.Input.noConfusionType => Physics.FlavorMajoranaCertificate.Input.noConfusionType,
  GUT.FlavorMajoranaCertificate.Input.nonnegative => Physics.FlavorMajoranaCertificate.Input.nonnegative,
  GUT.FlavorMajoranaCertificate.Input.normalization => Physics.FlavorMajoranaCertificate.Input.normalization,
  GUT.FlavorMajoranaCertificate.Input.rec => Physics.FlavorMajoranaCertificate.Input.rec,
  GUT.FlavorMajoranaCertificate.Input.recOn => Physics.FlavorMajoranaCertificate.Input.recOn,
  GUT.FlavorMajoranaCertificate.Input.symmetric => Physics.FlavorMajoranaCertificate.Input.symmetric,
  GUT.FlavorMajoranaCertificate.basisFreedom => Physics.FlavorMajoranaCertificate.basisFreedom,
  GUT.FlavorMajoranaCertificate.classification => Physics.FlavorMajoranaCertificate.classification,
  GUT.FlavorMajoranaCertificate.form => Physics.FlavorMajoranaCertificate.form,
  GUT.FlavorMajoranaCertificate.form_symmetric => Physics.FlavorMajoranaCertificate.form_symmetric,
  GUT.FlavorMajoranaCertificate.fromDiagonal => Physics.FlavorMajoranaCertificate.fromDiagonal,
  GUT.FlavorMajoranaCertificate.fromDiagonal_surjective => Physics.FlavorMajoranaCertificate.fromDiagonal_surjective,
  GUT.FlavorMajoranaCertificate.ofSymmetric => Physics.FlavorMajoranaCertificate.ofSymmetric,
  GUT.FlavorMajoranaCertificate.ofSymmetric_matrix => Physics.FlavorMajoranaCertificate.ofSymmetric_matrix,
  GUT.FlavorMajoranaCertificate.residualHomEquiv => Physics.FlavorMajoranaCertificate.residualHomEquiv,
  GUT.FlavorMajoranaCertificate.residual_nonzero_iff => Physics.FlavorMajoranaCertificate.residual_nonzero_iff,
  GUT.FlavorMajoranaCertificate.subgroup => Physics.FlavorMajoranaCertificate.subgroup,
  GUT.FlavorMajoranaCertificate.subgroup_eq => Physics.FlavorMajoranaCertificate.subgroup_eq
]

assert_compatible GUT.FlavorMajoranaCertificate.Input => Physics.FlavorMajoranaCertificate.Input
assert_compatible GUT.FlavorMajoranaCertificate.Input.basis => Physics.FlavorMajoranaCertificate.Input.basis
assert_compatible GUT.FlavorMajoranaCertificate.Input.casesOn => Physics.FlavorMajoranaCertificate.Input.casesOn
assert_compatible GUT.FlavorMajoranaCertificate.Input.ctorIdx => Physics.FlavorMajoranaCertificate.Input.ctorIdx
assert_compatible GUT.FlavorMajoranaCertificate.Input.mass => Physics.FlavorMajoranaCertificate.Input.mass
assert_compatible GUT.FlavorMajoranaCertificate.Input.matrix => Physics.FlavorMajoranaCertificate.Input.matrix
assert_compatible GUT.FlavorMajoranaCertificate.Input.mk => Physics.FlavorMajoranaCertificate.Input.mk
assert_compatible GUT.FlavorMajoranaCertificate.Input.mk.inj => Physics.FlavorMajoranaCertificate.Input.mk.inj
assert_compatible GUT.FlavorMajoranaCertificate.Input.mk.injEq => Physics.FlavorMajoranaCertificate.Input.mk.injEq
assert_compatible GUT.FlavorMajoranaCertificate.Input.mk.noConfusion => Physics.FlavorMajoranaCertificate.Input.mk.noConfusion
assert_compatible GUT.FlavorMajoranaCertificate.Input.mk.sizeOf_spec => Physics.FlavorMajoranaCertificate.Input.mk.sizeOf_spec
assert_compatible GUT.FlavorMajoranaCertificate.Input.noConfusion => Physics.FlavorMajoranaCertificate.Input.noConfusion
assert_compatible GUT.FlavorMajoranaCertificate.Input.noConfusionType => Physics.FlavorMajoranaCertificate.Input.noConfusionType
assert_compatible GUT.FlavorMajoranaCertificate.Input.nonnegative => Physics.FlavorMajoranaCertificate.Input.nonnegative
assert_compatible GUT.FlavorMajoranaCertificate.Input.normalization => Physics.FlavorMajoranaCertificate.Input.normalization
assert_compatible GUT.FlavorMajoranaCertificate.Input.rec => Physics.FlavorMajoranaCertificate.Input.rec
assert_compatible GUT.FlavorMajoranaCertificate.Input.recOn => Physics.FlavorMajoranaCertificate.Input.recOn
assert_compatible GUT.FlavorMajoranaCertificate.Input.symmetric => Physics.FlavorMajoranaCertificate.Input.symmetric
assert_compatible GUT.FlavorMajoranaCertificate.basisFreedom => Physics.FlavorMajoranaCertificate.basisFreedom
assert_compatible GUT.FlavorMajoranaCertificate.classification => Physics.FlavorMajoranaCertificate.classification
assert_compatible GUT.FlavorMajoranaCertificate.form => Physics.FlavorMajoranaCertificate.form
assert_compatible GUT.FlavorMajoranaCertificate.form_symmetric => Physics.FlavorMajoranaCertificate.form_symmetric
assert_compatible GUT.FlavorMajoranaCertificate.fromDiagonal => Physics.FlavorMajoranaCertificate.fromDiagonal
assert_compatible GUT.FlavorMajoranaCertificate.fromDiagonal_surjective => Physics.FlavorMajoranaCertificate.fromDiagonal_surjective
assert_compatible GUT.FlavorMajoranaCertificate.ofSymmetric => Physics.FlavorMajoranaCertificate.ofSymmetric
assert_compatible GUT.FlavorMajoranaCertificate.ofSymmetric_matrix => Physics.FlavorMajoranaCertificate.ofSymmetric_matrix
assert_compatible GUT.FlavorMajoranaCertificate.residualHomEquiv => Physics.FlavorMajoranaCertificate.residualHomEquiv
assert_compatible GUT.FlavorMajoranaCertificate.residual_nonzero_iff => Physics.FlavorMajoranaCertificate.residual_nonzero_iff
assert_compatible GUT.FlavorMajoranaCertificate.subgroup => Physics.FlavorMajoranaCertificate.subgroup
assert_compatible GUT.FlavorMajoranaCertificate.subgroup_eq => Physics.FlavorMajoranaCertificate.subgroup_eq
