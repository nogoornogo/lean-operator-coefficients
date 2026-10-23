import Physics.StandardModel.Operators.BaryonOne.Qque.BalancedSpeciesQque
import Physics.StandardModel.Spectrum.BalancedSpeciesExtension
import Physics.StandardModel.Operators.AutomaticSpeciesQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.BalancedSpeciesQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BalancedSpeciesQque.exists_actual_alternation => Physics.BalancedSpeciesQque.exists_actual_alternation,
  GUT.BalancedSpeciesQque.exists_actual_exterior => Physics.BalancedSpeciesQque.exists_actual_exterior
]

assert_compatible GUT.BalancedSpeciesQque.exists_actual_alternation => Physics.BalancedSpeciesQque.exists_actual_alternation
assert_compatible GUT.BalancedSpeciesQque.exists_actual_exterior => Physics.BalancedSpeciesQque.exists_actual_exterior
