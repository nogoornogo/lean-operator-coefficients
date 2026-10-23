import Physics.StandardModel.Operators.BaryonOne.Qque.CompactLightQque
import Physics.StandardModel.Operators.FourWeightLightQque
import Physics.FieldTheory.Mass.CompactResidualLightQuotient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.CompactLightQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CompactLightQque.common_quotient => Physics.CompactLightQque.common_quotient,
  GUT.CompactLightQque.exists_qque_coefficient => Physics.CompactLightQque.exists_qque_coefficient,
  GUT.CompactLightQque.not_forbidsBothInternalCoefficients => Physics.CompactLightQque.not_forbidsBothInternalCoefficients,
  GUT.CompactLightQque.radical_residual_continuous => Physics.CompactLightQque.radical_residual_continuous
]

assert_compatible GUT.CompactLightQque.common_quotient => Physics.CompactLightQque.common_quotient
assert_compatible GUT.CompactLightQque.exists_qque_coefficient => Physics.CompactLightQque.exists_qque_coefficient
assert_compatible GUT.CompactLightQque.not_forbidsBothInternalCoefficients => Physics.CompactLightQque.not_forbidsBothInternalCoefficients
assert_compatible GUT.CompactLightQque.radical_residual_continuous => Physics.CompactLightQque.radical_residual_continuous
