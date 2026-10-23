import Physics.StandardModel.Spectrum.Representations.ExactSMFourWeightTarget
import Physics.StandardModel.Spectrum.ExactSMWeightEvaluation
import Physics.StandardModel.Spectrum.MonitoredSMWeights
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ExactSMFourWeightTarget instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMFourWeightTarget.has_target => Physics.ExactSMFourWeightTarget.has_target,
  GUT.ExactSMFourWeightTarget.index_eq_multiplicity => Physics.ExactSMFourWeightTarget.index_eq_multiplicity
]

assert_compatible GUT.ExactSMFourWeightTarget.has_target => Physics.ExactSMFourWeightTarget.has_target
assert_compatible GUT.ExactSMFourWeightTarget.index_eq_multiplicity => Physics.ExactSMFourWeightTarget.index_eq_multiplicity
