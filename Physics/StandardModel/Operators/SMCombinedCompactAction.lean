import Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactAction
import Physics.StandardModel.Operators.SMMixedCompactCoefficients
import Math.RepresentationTheory.ProductInvariantCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMCombinedCompactAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCombinedCompactAction.Group => Physics.SMCombinedCompactAction.Group,
  GUT.SMCombinedCompactAction.Spin => Physics.SMCombinedCompactAction.Spin,
  GUT.SMCombinedCompactAction.action => Physics.SMCombinedCompactAction.action,
  GUT.SMCombinedCompactAction.action_gauge => Physics.SMCombinedCompactAction.action_gauge,
  GUT.SMCombinedCompactAction.action_spin => Physics.SMCombinedCompactAction.action_spin,
  GUT.SMCombinedCompactAction.boson => Physics.SMCombinedCompactAction.boson,
  GUT.SMCombinedCompactAction.coefficientEquiv => Physics.SMCombinedCompactAction.coefficientEquiv,
  GUT.SMCombinedCompactAction.field => Physics.SMCombinedCompactAction.field,
  GUT.SMCombinedCompactAction.field.eq_1 => Physics.SMCombinedCompactAction.field.eq_1,
  GUT.SMCombinedCompactAction.field_gauge => Physics.SMCombinedCompactAction.field_gauge,
  GUT.SMCombinedCompactAction.field_spin => Physics.SMCombinedCompactAction.field_spin,
  GUT.SMCombinedCompactAction.gaugeEmbedding => Physics.SMCombinedCompactAction.gaugeEmbedding,
  GUT.SMCombinedCompactAction.gaugeInclusion => Physics.SMCombinedCompactAction.gaugeInclusion,
  GUT.SMCombinedCompactAction.source => Physics.SMCombinedCompactAction.source,
  GUT.SMCombinedCompactAction.source_gauge => Physics.SMCombinedCompactAction.source_gauge,
  GUT.SMCombinedCompactAction.source_spin => Physics.SMCombinedCompactAction.source_spin,
  GUT.SMCombinedCompactAction.spinInclusion => Physics.SMCombinedCompactAction.spinInclusion
]

assert_compatible GUT.SMCombinedCompactAction.Group => Physics.SMCombinedCompactAction.Group
assert_compatible GUT.SMCombinedCompactAction.Spin => Physics.SMCombinedCompactAction.Spin
assert_compatible GUT.SMCombinedCompactAction.action => Physics.SMCombinedCompactAction.action
assert_compatible GUT.SMCombinedCompactAction.action_gauge => Physics.SMCombinedCompactAction.action_gauge
assert_compatible GUT.SMCombinedCompactAction.action_spin => Physics.SMCombinedCompactAction.action_spin
assert_compatible GUT.SMCombinedCompactAction.boson => Physics.SMCombinedCompactAction.boson
assert_compatible GUT.SMCombinedCompactAction.coefficientEquiv => Physics.SMCombinedCompactAction.coefficientEquiv
assert_compatible GUT.SMCombinedCompactAction.field => Physics.SMCombinedCompactAction.field
assert_compatible GUT.SMCombinedCompactAction.field.eq_1 => Physics.SMCombinedCompactAction.field.eq_1
assert_compatible GUT.SMCombinedCompactAction.field_gauge => Physics.SMCombinedCompactAction.field_gauge
assert_compatible GUT.SMCombinedCompactAction.field_spin => Physics.SMCombinedCompactAction.field_spin
assert_compatible GUT.SMCombinedCompactAction.gaugeEmbedding => Physics.SMCombinedCompactAction.gaugeEmbedding
assert_compatible GUT.SMCombinedCompactAction.gaugeInclusion => Physics.SMCombinedCompactAction.gaugeInclusion
assert_compatible GUT.SMCombinedCompactAction.source => Physics.SMCombinedCompactAction.source
assert_compatible GUT.SMCombinedCompactAction.source_gauge => Physics.SMCombinedCompactAction.source_gauge
assert_compatible GUT.SMCombinedCompactAction.source_spin => Physics.SMCombinedCompactAction.source_spin
assert_compatible GUT.SMCombinedCompactAction.spinInclusion => Physics.SMCombinedCompactAction.spinInclusion
