import Physics.StandardModel.Operators.BaryonOne.Qque.LightSMSpeciesQque
import Physics.StandardModel.Spectrum.LightSMSpeciesIndex
import Physics.StandardModel.Operators.QqueSpinorExterior
import Physics.StandardModel.Gauge.LightSMFieldExtraction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.LightSMSpeciesQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LightSMSpeciesQque.HasActualExterior => Physics.LightSMSpeciesQque.HasActualExterior,
  GUT.LightSMSpeciesQque.exists_actual_alternation => Physics.LightSMSpeciesQque.exists_actual_alternation,
  GUT.LightSMSpeciesQque.exists_actual_exterior => Physics.LightSMSpeciesQque.exists_actual_exterior,
  GUT.LightSMSpeciesQque.exists_model_exterior => Physics.LightSMSpeciesQque.exists_model_exterior
]

assert_compatible GUT.LightSMSpeciesQque.HasActualExterior => Physics.LightSMSpeciesQque.HasActualExterior
assert_compatible GUT.LightSMSpeciesQque.exists_actual_alternation => Physics.LightSMSpeciesQque.exists_actual_alternation
assert_compatible GUT.LightSMSpeciesQque.exists_actual_exterior => Physics.LightSMSpeciesQque.exists_actual_exterior
assert_compatible GUT.LightSMSpeciesQque.exists_model_exterior => Physics.LightSMSpeciesQque.exists_model_exterior
