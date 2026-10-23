import Physics.StandardModel.Operators.BaryonOne.Qque.AutomaticSpeciesQque
import Physics.StandardModel.Spectrum.AutomaticSMSpeciesIndex
import Physics.StandardModel.Operators.PairwisePositiveQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.AutomaticSpeciesQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AutomaticSpeciesQque.exists_actual_alternation => Physics.AutomaticSpeciesQque.exists_actual_alternation,
  GUT.AutomaticSpeciesQque.exists_actual_exterior => Physics.AutomaticSpeciesQque.exists_actual_exterior
]

assert_compatible GUT.AutomaticSpeciesQque.exists_actual_alternation => Physics.AutomaticSpeciesQque.exists_actual_alternation
assert_compatible GUT.AutomaticSpeciesQque.exists_actual_exterior => Physics.AutomaticSpeciesQque.exists_actual_exterior
