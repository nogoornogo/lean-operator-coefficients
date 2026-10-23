import Physics.FieldTheory.Mass.Algebra.CompactResidualLightQuotient
import Physics.FieldTheory.Mass.ResidualMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.CompactResidualLightQuotient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CompactResidualLightQuotient.exists_common_quotient => Physics.CompactResidualLightQuotient.exists_common_quotient,
  GUT.CompactResidualLightQuotient.exists_split_of_index_eq => Physics.CompactResidualLightQuotient.exists_split_of_index_eq
]

assert_compatible GUT.CompactResidualLightQuotient.exists_common_quotient => Physics.CompactResidualLightQuotient.exists_common_quotient
assert_compatible GUT.CompactResidualLightQuotient.exists_split_of_index_eq => Physics.CompactResidualLightQuotient.exists_split_of_index_eq
