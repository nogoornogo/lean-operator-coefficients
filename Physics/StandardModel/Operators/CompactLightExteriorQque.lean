import Physics.StandardModel.Operators.BaryonOne.Qque.CompactLightExteriorQque
import Physics.StandardModel.Gauge.CompactExplicitSMTensor
import Physics.StandardModel.Operators.QqueSpinorExterior
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.CompactLightExteriorQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CompactLightExteriorQque.exists_ordered_nonzero_exterior => Physics.CompactLightExteriorQque.exists_ordered_nonzero_exterior,
  GUT.CompactLightExteriorQque.exists_qque => Physics.CompactLightExteriorQque.exists_qque
]

assert_compatible GUT.CompactLightExteriorQque.exists_ordered_nonzero_exterior => Physics.CompactLightExteriorQque.exists_ordered_nonzero_exterior
assert_compatible GUT.CompactLightExteriorQque.exists_qque => Physics.CompactLightExteriorQque.exists_qque
