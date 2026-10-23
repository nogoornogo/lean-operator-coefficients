import Physics.FieldTheory.Mass.Algebra.ResidualLightQuotient
import Physics.FieldTheory.Mass.ResidualMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.ResidualLightQuotient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ResidualLightQuotient.exists_common_quotient => Physics.ResidualLightQuotient.exists_common_quotient,
  GUT.ResidualLightQuotient.exists_split_of_index_eq => Physics.ResidualLightQuotient.exists_split_of_index_eq
]

assert_compatible GUT.ResidualLightQuotient.exists_common_quotient => Physics.ResidualLightQuotient.exists_common_quotient
assert_compatible GUT.ResidualLightQuotient.exists_split_of_index_eq => Physics.ResidualLightQuotient.exists_split_of_index_eq
