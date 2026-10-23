import Physics.StandardModel.Operators.BaryonOne.Qque.FullLightRadicalQque
import Physics.StandardModel.Operators.FullLightSpeciesQque
import Physics.StandardModel.Gauge.LightSMAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.FullLightRadicalQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FullLightRadicalQque.all_forbidden_iff => Physics.FullLightRadicalQque.all_forbidden_iff,
  GUT.FullLightRadicalQque.all_forbidden_iff_of_jointlyContinuous => Physics.FullLightRadicalQque.all_forbidden_iff_of_jointlyContinuous,
  GUT.FullLightRadicalQque.equiv => Physics.FullLightRadicalQque.equiv,
  GUT.FullLightRadicalQque.nonzero_iff => Physics.FullLightRadicalQque.nonzero_iff,
  GUT.FullLightRadicalQque.nonzero_iff_of_jointlyContinuous => Physics.FullLightRadicalQque.nonzero_iff_of_jointlyContinuous,
  GUT.FullLightRadicalQque.sm_semisimple => Physics.FullLightRadicalQque.sm_semisimple
]

assert_compatible GUT.FullLightRadicalQque.all_forbidden_iff => Physics.FullLightRadicalQque.all_forbidden_iff
assert_compatible GUT.FullLightRadicalQque.all_forbidden_iff_of_jointlyContinuous => Physics.FullLightRadicalQque.all_forbidden_iff_of_jointlyContinuous
assert_compatible GUT.FullLightRadicalQque.equiv => Physics.FullLightRadicalQque.equiv
assert_compatible GUT.FullLightRadicalQque.nonzero_iff => Physics.FullLightRadicalQque.nonzero_iff
assert_compatible GUT.FullLightRadicalQque.nonzero_iff_of_jointlyContinuous => Physics.FullLightRadicalQque.nonzero_iff_of_jointlyContinuous
assert_compatible GUT.FullLightRadicalQque.sm_semisimple => Physics.FullLightRadicalQque.sm_semisimple
