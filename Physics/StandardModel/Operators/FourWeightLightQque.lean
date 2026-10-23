import Physics.StandardModel.Operators.BaryonOne.Qque.FourWeightLightQque
import Physics.StandardModel.Operators.NonabelianLightOperators
import Physics.StandardModel.Spectrum.QqueLocalTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.FourWeightLightQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourWeightLightQque.HasTarget => Physics.FourWeightLightQque.HasTarget,
  GUT.FourWeightLightQque.characters_compatible => Physics.FourWeightLightQque.characters_compatible,
  GUT.FourWeightLightQque.common_quotient => Physics.FourWeightLightQque.common_quotient,
  GUT.FourWeightLightQque.exists_qque_coefficient => Physics.FourWeightLightQque.exists_qque_coefficient,
  GUT.FourWeightLightQque.not_forbidsBothInternalCoefficients => Physics.FourWeightLightQque.not_forbidsBothInternalCoefficients,
  GUT.FourWeightLightQque.of_matches => Physics.FourWeightLightQque.of_matches,
  GUT.FourWeightLightQque.target_iff_of_characters_eq => Physics.FourWeightLightQque.target_iff_of_characters_eq
]

assert_compatible GUT.FourWeightLightQque.HasTarget => Physics.FourWeightLightQque.HasTarget
assert_compatible GUT.FourWeightLightQque.characters_compatible => Physics.FourWeightLightQque.characters_compatible
assert_compatible GUT.FourWeightLightQque.common_quotient => Physics.FourWeightLightQque.common_quotient
assert_compatible GUT.FourWeightLightQque.exists_qque_coefficient => Physics.FourWeightLightQque.exists_qque_coefficient
assert_compatible GUT.FourWeightLightQque.not_forbidsBothInternalCoefficients => Physics.FourWeightLightQque.not_forbidsBothInternalCoefficients
assert_compatible GUT.FourWeightLightQque.of_matches => Physics.FourWeightLightQque.of_matches
assert_compatible GUT.FourWeightLightQque.target_iff_of_characters_eq => Physics.FourWeightLightQque.target_iff_of_characters_eq
