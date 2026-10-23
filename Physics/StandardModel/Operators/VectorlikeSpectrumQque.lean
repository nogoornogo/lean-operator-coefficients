import Physics.StandardModel.Operators.BaryonOne.Qque.VectorlikeSpectrumQque
import Physics.StandardModel.Operators.BalancedSpeciesQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.VectorlikeSpectrumQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.VectorlikeSpectrumQque.exists_actual_exterior => Physics.VectorlikeSpectrumQque.exists_actual_exterior,
  GUT.VectorlikeSpectrumQque.extension => Physics.VectorlikeSpectrumQque.extension,
  GUT.VectorlikeSpectrumQque.shared_positive => Physics.VectorlikeSpectrumQque.shared_positive
]

assert_compatible GUT.VectorlikeSpectrumQque.exists_actual_exterior => Physics.VectorlikeSpectrumQque.exists_actual_exterior
assert_compatible GUT.VectorlikeSpectrumQque.extension => Physics.VectorlikeSpectrumQque.extension
assert_compatible GUT.VectorlikeSpectrumQque.shared_positive => Physics.VectorlikeSpectrumQque.shared_positive
