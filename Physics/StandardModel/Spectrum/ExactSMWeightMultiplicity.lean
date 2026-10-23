import Physics.StandardModel.Spectrum.Representations.ExactSMWeightMultiplicity
import Physics.StandardModel.Spectrum.ExactSMResidualSpectrum
import Physics.StandardModel.Spectrum.GaugeTorusTrace
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ExactSMWeightMultiplicity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMWeightMultiplicity.action_trace => Physics.ExactSMWeightMultiplicity.action_trace,
  GUT.ExactSMWeightMultiplicity.coefficients_eq => Physics.ExactSMWeightMultiplicity.coefficients_eq,
  GUT.ExactSMWeightMultiplicity.eval_polynomial => Physics.ExactSMWeightMultiplicity.eval_polynomial,
  GUT.ExactSMWeightMultiplicity.generation_trace => Physics.ExactSMWeightMultiplicity.generation_trace,
  GUT.ExactSMWeightMultiplicity.opposite_weight_finrank => Physics.ExactSMWeightMultiplicity.opposite_weight_finrank,
  GUT.ExactSMWeightMultiplicity.polynomial => Physics.ExactSMWeightMultiplicity.polynomial,
  GUT.ExactSMWeightMultiplicity.polynomial.eq_1 => Physics.ExactSMWeightMultiplicity.polynomial.eq_1,
  GUT.ExactSMWeightMultiplicity.polynomial_negative => Physics.ExactSMWeightMultiplicity.polynomial_negative,
  GUT.ExactSMWeightMultiplicity.polynomial_positive => Physics.ExactSMWeightMultiplicity.polynomial_positive,
  GUT.ExactSMWeightMultiplicity.weight_finrank => Physics.ExactSMWeightMultiplicity.weight_finrank,
  GUT.ExactSMWeightMultiplicity.weight_neg => Physics.ExactSMWeightMultiplicity.weight_neg,
  GUT.ExactSMWeightMultiplicity.weight_zero => Physics.ExactSMWeightMultiplicity.weight_zero,
  GUT.StandardSMCharacterTarget.smReducedWeight.eq_1 => Physics.StandardSMCharacterTarget.smReducedWeight.eq_1
]

assert_compatible GUT.ExactSMWeightMultiplicity.action_trace => Physics.ExactSMWeightMultiplicity.action_trace
assert_compatible GUT.ExactSMWeightMultiplicity.coefficients_eq => Physics.ExactSMWeightMultiplicity.coefficients_eq
assert_compatible GUT.ExactSMWeightMultiplicity.eval_polynomial => Physics.ExactSMWeightMultiplicity.eval_polynomial
assert_compatible GUT.ExactSMWeightMultiplicity.generation_trace => Physics.ExactSMWeightMultiplicity.generation_trace
assert_compatible GUT.ExactSMWeightMultiplicity.opposite_weight_finrank => Physics.ExactSMWeightMultiplicity.opposite_weight_finrank
assert_compatible GUT.ExactSMWeightMultiplicity.polynomial => Physics.ExactSMWeightMultiplicity.polynomial
assert_compatible GUT.ExactSMWeightMultiplicity.polynomial.eq_1 => Physics.ExactSMWeightMultiplicity.polynomial.eq_1
assert_compatible GUT.ExactSMWeightMultiplicity.polynomial_negative => Physics.ExactSMWeightMultiplicity.polynomial_negative
assert_compatible GUT.ExactSMWeightMultiplicity.polynomial_positive => Physics.ExactSMWeightMultiplicity.polynomial_positive
assert_compatible GUT.ExactSMWeightMultiplicity.weight_finrank => Physics.ExactSMWeightMultiplicity.weight_finrank
assert_compatible GUT.ExactSMWeightMultiplicity.weight_neg => Physics.ExactSMWeightMultiplicity.weight_neg
assert_compatible GUT.ExactSMWeightMultiplicity.weight_zero => Physics.ExactSMWeightMultiplicity.weight_zero
assert_compatible GUT.StandardSMCharacterTarget.smReducedWeight.eq_1 => Physics.StandardSMCharacterTarget.smReducedWeight.eq_1
