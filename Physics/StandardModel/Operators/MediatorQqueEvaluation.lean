import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQqueEvaluation
import Physics.StandardModel.Operators.MediatorQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQqueEvaluation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MediatorQqueEvaluation.sector_ne_zero_of_restriction => Physics.MediatorQqueEvaluation.sector_ne_zero_of_restriction,
  GUT.MediatorQqueEvaluation.sector_ne_zero_of_slots => Physics.MediatorQqueEvaluation.sector_ne_zero_of_slots,
  GUT.MediatorQqueEvaluation.sector_slots => Physics.MediatorQqueEvaluation.sector_slots
]

assert_compatible GUT.MediatorQqueEvaluation.sector_ne_zero_of_restriction => Physics.MediatorQqueEvaluation.sector_ne_zero_of_restriction
assert_compatible GUT.MediatorQqueEvaluation.sector_ne_zero_of_slots => Physics.MediatorQqueEvaluation.sector_ne_zero_of_slots
assert_compatible GUT.MediatorQqueEvaluation.sector_slots => Physics.MediatorQqueEvaluation.sector_slots
