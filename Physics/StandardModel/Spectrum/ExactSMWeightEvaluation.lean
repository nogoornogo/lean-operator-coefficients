import Physics.StandardModel.Spectrum.Representations.ExactSMWeightEvaluation
import Physics.StandardModel.Spectrum.ExactSMWeightMultiplicity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ExactSMWeightEvaluation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMWeightEvaluation.evaluation => Physics.ExactSMWeightEvaluation.evaluation,
  GUT.ExactSMWeightEvaluation.evaluationEquiv => Physics.ExactSMWeightEvaluation.evaluationEquiv,
  GUT.ExactSMWeightEvaluation.evaluation_injective => Physics.ExactSMWeightEvaluation.evaluation_injective
]

assert_compatible GUT.ExactSMWeightEvaluation.evaluation => Physics.ExactSMWeightEvaluation.evaluation
assert_compatible GUT.ExactSMWeightEvaluation.evaluationEquiv => Physics.ExactSMWeightEvaluation.evaluationEquiv
assert_compatible GUT.ExactSMWeightEvaluation.evaluation_injective => Physics.ExactSMWeightEvaluation.evaluation_injective
