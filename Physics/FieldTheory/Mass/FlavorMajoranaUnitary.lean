import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaUnitary
import Physics.FieldTheory.Mass.FlavorMajoranaDiagonal
import Math.LinearAlgebra.MajoranaUnitaryClassification
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Flavor.FlavorMajoranaUnitary instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavorMajoranaUnitary.action => Physics.FlavorMajoranaUnitary.action,
  GUT.FlavorMajoranaUnitary.classification => Physics.FlavorMajoranaUnitary.classification,
  GUT.FlavorMajoranaUnitary.form_matrix => Physics.FlavorMajoranaUnitary.form_matrix,
  GUT.FlavorMajoranaUnitary.residualHomEquiv => Physics.FlavorMajoranaUnitary.residualHomEquiv,
  GUT.FlavorMajoranaUnitary.residual_nonzero_iff => Physics.FlavorMajoranaUnitary.residual_nonzero_iff,
  GUT.FlavorMajoranaUnitary.subgroup => Physics.FlavorMajoranaUnitary.subgroup,
  GUT.FlavorMajoranaUnitary.subgroup_eq => Physics.FlavorMajoranaUnitary.subgroup_eq
]

assert_compatible GUT.FlavorMajoranaUnitary.action => Physics.FlavorMajoranaUnitary.action
assert_compatible GUT.FlavorMajoranaUnitary.classification => Physics.FlavorMajoranaUnitary.classification
assert_compatible GUT.FlavorMajoranaUnitary.form_matrix => Physics.FlavorMajoranaUnitary.form_matrix
assert_compatible GUT.FlavorMajoranaUnitary.residualHomEquiv => Physics.FlavorMajoranaUnitary.residualHomEquiv
assert_compatible GUT.FlavorMajoranaUnitary.residual_nonzero_iff => Physics.FlavorMajoranaUnitary.residual_nonzero_iff
assert_compatible GUT.FlavorMajoranaUnitary.subgroup => Physics.FlavorMajoranaUnitary.subgroup
assert_compatible GUT.FlavorMajoranaUnitary.subgroup_eq => Physics.FlavorMajoranaUnitary.subgroup_eq
