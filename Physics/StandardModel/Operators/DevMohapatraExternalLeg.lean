import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraExternalLeg
import Physics.StandardModel.Operators.DevMohapatraLiteratureConvention
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraExternalLeg instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraExternalLeg.completedAction => Physics.DevMohapatraExternalLeg.completedAction,
  GUT.DevMohapatraExternalLeg.completedAction.eq_1 => Physics.DevMohapatraExternalLeg.completedAction.eq_1,
  GUT.DevMohapatraExternalLeg.completion_projection => Physics.DevMohapatraExternalLeg.completion_projection,
  GUT.DevMohapatraExternalLeg.completion_projection_free => Physics.DevMohapatraExternalLeg.completion_projection_free,
  GUT.DevMohapatraExternalLeg.fixed_leg => Physics.DevMohapatraExternalLeg.fixed_leg,
  GUT.DevMohapatraExternalLeg.inverse_left => Physics.DevMohapatraExternalLeg.inverse_left,
  GUT.DevMohapatraExternalLeg.inverse_right => Physics.DevMohapatraExternalLeg.inverse_right,
  GUT.DevMohapatraExternalLeg.massInverse => Physics.DevMohapatraExternalLeg.massInverse,
  GUT.DevMohapatraExternalLeg.massInverse.eq_1 => Physics.DevMohapatraExternalLeg.massInverse.eq_1,
  GUT.DevMohapatraExternalLeg.massKernel => Physics.DevMohapatraExternalLeg.massKernel,
  GUT.DevMohapatraExternalLeg.massKernel.eq_1 => Physics.DevMohapatraExternalLeg.massKernel.eq_1,
  GUT.DevMohapatraExternalLeg.mass_action => Physics.DevMohapatraExternalLeg.mass_action,
  GUT.DevMohapatraExternalLeg.sewn => Physics.DevMohapatraExternalLeg.sewn,
  GUT.DevMohapatraExternalLeg.sewn.eq_1 => Physics.DevMohapatraExternalLeg.sewn.eq_1,
  GUT.DevMohapatraExternalLeg.sewn_current => Physics.DevMohapatraExternalLeg.sewn_current,
  GUT.DevMohapatraExternalLeg.sewn_generated => Physics.DevMohapatraExternalLeg.sewn_generated,
  GUT.DevMohapatraExternalLeg.sewn_uv => Physics.DevMohapatraExternalLeg.sewn_uv,
  GUT.DevMohapatraExternalLeg.source => Physics.DevMohapatraExternalLeg.source,
  GUT.DevMohapatraExternalLeg.source.eq_1 => Physics.DevMohapatraExternalLeg.source.eq_1
]

assert_compatible GUT.DevMohapatraExternalLeg.completedAction => Physics.DevMohapatraExternalLeg.completedAction
assert_compatible GUT.DevMohapatraExternalLeg.completedAction.eq_1 => Physics.DevMohapatraExternalLeg.completedAction.eq_1
assert_compatible GUT.DevMohapatraExternalLeg.completion_projection => Physics.DevMohapatraExternalLeg.completion_projection
assert_compatible GUT.DevMohapatraExternalLeg.completion_projection_free => Physics.DevMohapatraExternalLeg.completion_projection_free
assert_compatible GUT.DevMohapatraExternalLeg.fixed_leg => Physics.DevMohapatraExternalLeg.fixed_leg
assert_compatible GUT.DevMohapatraExternalLeg.inverse_left => Physics.DevMohapatraExternalLeg.inverse_left
assert_compatible GUT.DevMohapatraExternalLeg.inverse_right => Physics.DevMohapatraExternalLeg.inverse_right
assert_compatible GUT.DevMohapatraExternalLeg.massInverse => Physics.DevMohapatraExternalLeg.massInverse
assert_compatible GUT.DevMohapatraExternalLeg.massInverse.eq_1 => Physics.DevMohapatraExternalLeg.massInverse.eq_1
assert_compatible GUT.DevMohapatraExternalLeg.massKernel => Physics.DevMohapatraExternalLeg.massKernel
assert_compatible GUT.DevMohapatraExternalLeg.massKernel.eq_1 => Physics.DevMohapatraExternalLeg.massKernel.eq_1
assert_compatible GUT.DevMohapatraExternalLeg.mass_action => Physics.DevMohapatraExternalLeg.mass_action
assert_compatible GUT.DevMohapatraExternalLeg.sewn => Physics.DevMohapatraExternalLeg.sewn
assert_compatible GUT.DevMohapatraExternalLeg.sewn.eq_1 => Physics.DevMohapatraExternalLeg.sewn.eq_1
assert_compatible GUT.DevMohapatraExternalLeg.sewn_current => Physics.DevMohapatraExternalLeg.sewn_current
assert_compatible GUT.DevMohapatraExternalLeg.sewn_generated => Physics.DevMohapatraExternalLeg.sewn_generated
assert_compatible GUT.DevMohapatraExternalLeg.sewn_uv => Physics.DevMohapatraExternalLeg.sewn_uv
assert_compatible GUT.DevMohapatraExternalLeg.source => Physics.DevMohapatraExternalLeg.source
assert_compatible GUT.DevMohapatraExternalLeg.source.eq_1 => Physics.DevMohapatraExternalLeg.source.eq_1
