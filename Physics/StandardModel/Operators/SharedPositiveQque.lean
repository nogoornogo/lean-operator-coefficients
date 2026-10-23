import Physics.StandardModel.Operators.BaryonOne.Qque.SharedPositiveQque
import Physics.StandardModel.Spectrum.SharedPositiveSpeciesIndex
import Physics.StandardModel.Operators.LightSMSpeciesQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.SharedPositiveQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SharedPositiveQque.exists_actual_alternation => Physics.SharedPositiveQque.exists_actual_alternation,
  GUT.SharedPositiveQque.exists_actual_exterior => Physics.SharedPositiveQque.exists_actual_exterior
]

assert_compatible GUT.SharedPositiveQque.exists_actual_alternation => Physics.SharedPositiveQque.exists_actual_alternation
assert_compatible GUT.SharedPositiveQque.exists_actual_exterior => Physics.SharedPositiveQque.exists_actual_exterior
