import Physics.StandardModel.Operators.Support.Coordinates.SMIntegralLocalWeights
import Physics.StandardModel.Operators.SMColorIntegralBasis
import Physics.StandardModel.Operators.SMWeylFiniteKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMIntegralLocalWeights instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMIntegralLocalWeights.Group => Physics.SMIntegralLocalWeights.Group,
  GUT.SMIntegralLocalWeights.action => Physics.SMIntegralLocalWeights.action,
  GUT.SMIntegralLocalWeights.action_color => Physics.SMIntegralLocalWeights.action_color,
  GUT.SMIntegralLocalWeights.action_hyper => Physics.SMIntegralLocalWeights.action_hyper,
  GUT.SMIntegralLocalWeights.action_weak => Physics.SMIntegralLocalWeights.action_weak,
  GUT.SMIntegralLocalWeights.boson => Physics.SMIntegralLocalWeights.boson,
  GUT.SMIntegralLocalWeights.boson_color => Physics.SMIntegralLocalWeights.boson_color,
  GUT.SMIntegralLocalWeights.boson_hyper => Physics.SMIntegralLocalWeights.boson_hyper,
  GUT.SMIntegralLocalWeights.boson_weak => Physics.SMIntegralLocalWeights.boson_weak,
  GUT.SMIntegralLocalWeights.color => Physics.SMIntegralLocalWeights.color,
  GUT.SMIntegralLocalWeights.color.eq_1 => Physics.SMIntegralLocalWeights.color.eq_1,
  GUT.SMIntegralLocalWeights.colorTorus => Physics.SMIntegralLocalWeights.colorTorus,
  GUT.SMIntegralLocalWeights.colorTorus.eq_1 => Physics.SMIntegralLocalWeights.colorTorus.eq_1,
  GUT.SMIntegralLocalWeights.hyper => Physics.SMIntegralLocalWeights.hyper,
  GUT.SMIntegralLocalWeights.source => Physics.SMIntegralLocalWeights.source,
  GUT.SMIntegralLocalWeights.source_color => Physics.SMIntegralLocalWeights.source_color,
  GUT.SMIntegralLocalWeights.source_hyper => Physics.SMIntegralLocalWeights.source_hyper,
  GUT.SMIntegralLocalWeights.source_weak => Physics.SMIntegralLocalWeights.source_weak,
  GUT.SMIntegralLocalWeights.spin => Physics.SMIntegralLocalWeights.spin,
  GUT.SMIntegralLocalWeights.weak => Physics.SMIntegralLocalWeights.weak,
  GUT.SMIntegralLocalWeights.weak.eq_1 => Physics.SMIntegralLocalWeights.weak.eq_1,
  GUT.SMIntegralLocalWeights.weakTorus => Physics.SMIntegralLocalWeights.weakTorus,
  GUT.SMIntegralLocalWeights.weakTorus.eq_1 => Physics.SMIntegralLocalWeights.weakTorus.eq_1
]

assert_compatible GUT.SMIntegralLocalWeights.Group => Physics.SMIntegralLocalWeights.Group
assert_compatible GUT.SMIntegralLocalWeights.action => Physics.SMIntegralLocalWeights.action
assert_compatible GUT.SMIntegralLocalWeights.action_color => Physics.SMIntegralLocalWeights.action_color
assert_compatible GUT.SMIntegralLocalWeights.action_hyper => Physics.SMIntegralLocalWeights.action_hyper
assert_compatible GUT.SMIntegralLocalWeights.action_weak => Physics.SMIntegralLocalWeights.action_weak
assert_compatible GUT.SMIntegralLocalWeights.boson => Physics.SMIntegralLocalWeights.boson
assert_compatible GUT.SMIntegralLocalWeights.boson_color => Physics.SMIntegralLocalWeights.boson_color
assert_compatible GUT.SMIntegralLocalWeights.boson_hyper => Physics.SMIntegralLocalWeights.boson_hyper
assert_compatible GUT.SMIntegralLocalWeights.boson_weak => Physics.SMIntegralLocalWeights.boson_weak
assert_compatible GUT.SMIntegralLocalWeights.color => Physics.SMIntegralLocalWeights.color
assert_compatible GUT.SMIntegralLocalWeights.color.eq_1 => Physics.SMIntegralLocalWeights.color.eq_1
assert_compatible GUT.SMIntegralLocalWeights.colorTorus => Physics.SMIntegralLocalWeights.colorTorus
assert_compatible GUT.SMIntegralLocalWeights.colorTorus.eq_1 => Physics.SMIntegralLocalWeights.colorTorus.eq_1
assert_compatible GUT.SMIntegralLocalWeights.hyper => Physics.SMIntegralLocalWeights.hyper
assert_compatible GUT.SMIntegralLocalWeights.source => Physics.SMIntegralLocalWeights.source
assert_compatible GUT.SMIntegralLocalWeights.source_color => Physics.SMIntegralLocalWeights.source_color
assert_compatible GUT.SMIntegralLocalWeights.source_hyper => Physics.SMIntegralLocalWeights.source_hyper
assert_compatible GUT.SMIntegralLocalWeights.source_weak => Physics.SMIntegralLocalWeights.source_weak
assert_compatible GUT.SMIntegralLocalWeights.spin => Physics.SMIntegralLocalWeights.spin
assert_compatible GUT.SMIntegralLocalWeights.weak => Physics.SMIntegralLocalWeights.weak
assert_compatible GUT.SMIntegralLocalWeights.weak.eq_1 => Physics.SMIntegralLocalWeights.weak.eq_1
assert_compatible GUT.SMIntegralLocalWeights.weakTorus => Physics.SMIntegralLocalWeights.weakTorus
assert_compatible GUT.SMIntegralLocalWeights.weakTorus.eq_1 => Physics.SMIntegralLocalWeights.weakTorus.eq_1
