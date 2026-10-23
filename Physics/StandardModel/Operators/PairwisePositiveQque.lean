import Physics.StandardModel.Operators.BaryonOne.Qque.PairwisePositiveQque
import Physics.StandardModel.Spectrum.PairwisePositiveSpeciesIndex
import Physics.StandardModel.Operators.PairwiseQqueSpinorExterior
import Physics.StandardModel.Operators.LightSMSpeciesQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.PairwisePositiveQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairwisePositiveQque.exists_actual_alternation => Physics.PairwisePositiveQque.exists_actual_alternation,
  GUT.PairwisePositiveQque.exists_actual_exterior => Physics.PairwisePositiveQque.exists_actual_exterior
]

assert_compatible GUT.PairwisePositiveQque.exists_actual_alternation => Physics.PairwisePositiveQque.exists_actual_alternation
assert_compatible GUT.PairwisePositiveQque.exists_actual_exterior => Physics.PairwisePositiveQque.exists_actual_exterior
