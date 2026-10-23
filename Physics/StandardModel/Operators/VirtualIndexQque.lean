import Physics.StandardModel.Operators.BaryonOne.Qque.VirtualIndexQque
import Physics.StandardModel.Spectrum.VirtualSMSpeciesIndex
import Physics.StandardModel.Operators.LightSMSpeciesQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.VirtualIndexQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.VirtualIndexQque.exists_actual_alternation => Physics.VirtualIndexQque.exists_actual_alternation,
  GUT.VirtualIndexQque.exists_actual_alternation_of_common_index => Physics.VirtualIndexQque.exists_actual_alternation_of_common_index,
  GUT.VirtualIndexQque.exists_actual_exterior => Physics.VirtualIndexQque.exists_actual_exterior
]

assert_compatible GUT.VirtualIndexQque.exists_actual_alternation => Physics.VirtualIndexQque.exists_actual_alternation
assert_compatible GUT.VirtualIndexQque.exists_actual_alternation_of_common_index => Physics.VirtualIndexQque.exists_actual_alternation_of_common_index
assert_compatible GUT.VirtualIndexQque.exists_actual_exterior => Physics.VirtualIndexQque.exists_actual_exterior
