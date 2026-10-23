import Physics.StandardModel.Spectrum.Representations.ExactSMAutomaticPositive
import Physics.StandardModel.Spectrum.AutomaticSMSpeciesIndex
import Physics.StandardModel.Spectrum.ExactSMFourWeightTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ExactSMAutomaticPositive instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMAutomaticPositive.pairwise_positive => Physics.ExactSMAutomaticPositive.pairwise_positive,
  GUT.ExactSMAutomaticPositive.shared_positive => Physics.ExactSMAutomaticPositive.shared_positive
]

assert_compatible GUT.ExactSMAutomaticPositive.pairwise_positive => Physics.ExactSMAutomaticPositive.pairwise_positive
assert_compatible GUT.ExactSMAutomaticPositive.shared_positive => Physics.ExactSMAutomaticPositive.shared_positive
