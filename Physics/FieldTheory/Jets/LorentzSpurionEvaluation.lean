import Physics.FieldTheory.Jets.Lorentz.LorentzSpurionEvaluation
import Math.RepresentationTheory.JetSpurionEvaluation
import Physics.FieldTheory.Jets.LorentzDirections
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lorentz.LorentzSpurionEvaluation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzSpurionEvaluation.Coefficients => Physics.LorentzSpurionEvaluation.Coefficients,
  GUT.LorentzSpurionEvaluation.Source => Physics.LorentzSpurionEvaluation.Source,
  GUT.LorentzSpurionEvaluation.action => Physics.LorentzSpurionEvaluation.action,
  GUT.LorentzSpurionEvaluation.card_surjective => Physics.LorentzSpurionEvaluation.card_surjective,
  GUT.LorentzSpurionEvaluation.coefficientEquiv => Physics.LorentzSpurionEvaluation.coefficientEquiv,
  GUT.LorentzSpurionEvaluation.evaluation => Physics.LorentzSpurionEvaluation.evaluation,
  GUT.LorentzSpurionEvaluation.nonzero_iff => Physics.LorentzSpurionEvaluation.nonzero_iff,
  GUT.LorentzSpurionEvaluation.pullback_injective => Physics.LorentzSpurionEvaluation.pullback_injective,
  GUT.LorentzSpurionEvaluation.sourceEquiv => Physics.LorentzSpurionEvaluation.sourceEquiv,
  GUT.LorentzSpurionEvaluation.surjective => Physics.LorentzSpurionEvaluation.surjective
]

assert_compatible GUT.LorentzSpurionEvaluation.Coefficients => Physics.LorentzSpurionEvaluation.Coefficients
assert_compatible GUT.LorentzSpurionEvaluation.Source => Physics.LorentzSpurionEvaluation.Source
assert_compatible GUT.LorentzSpurionEvaluation.action => Physics.LorentzSpurionEvaluation.action
assert_compatible GUT.LorentzSpurionEvaluation.card_surjective => Physics.LorentzSpurionEvaluation.card_surjective
assert_compatible GUT.LorentzSpurionEvaluation.coefficientEquiv => Physics.LorentzSpurionEvaluation.coefficientEquiv
assert_compatible GUT.LorentzSpurionEvaluation.evaluation => Physics.LorentzSpurionEvaluation.evaluation
assert_compatible GUT.LorentzSpurionEvaluation.nonzero_iff => Physics.LorentzSpurionEvaluation.nonzero_iff
assert_compatible GUT.LorentzSpurionEvaluation.pullback_injective => Physics.LorentzSpurionEvaluation.pullback_injective
assert_compatible GUT.LorentzSpurionEvaluation.sourceEquiv => Physics.LorentzSpurionEvaluation.sourceEquiv
assert_compatible GUT.LorentzSpurionEvaluation.surjective => Physics.LorentzSpurionEvaluation.surjective
