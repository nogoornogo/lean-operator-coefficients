import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoCyclicSelection
import Physics.StandardModel.Operators.DeltaBTwoScalarSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoCyclicSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaBTwoCyclicSelection.allowed_iff => Physics.DeltaBTwoCyclicSelection.allowed_iff,
  GUT.DeltaBTwoCyclicSelection.charge => Physics.DeltaBTwoCyclicSelection.charge,
  GUT.DeltaBTwoCyclicSelection.charge.eq_1 => Physics.DeltaBTwoCyclicSelection.charge.eq_1,
  GUT.DeltaBTwoCyclicSelection.forbidBoth => Physics.DeltaBTwoCyclicSelection.forbidBoth,
  GUT.DeltaBTwoCyclicSelection.forbidBoth_conditions => Physics.DeltaBTwoCyclicSelection.forbidBoth_conditions,
  GUT.DeltaBTwoCyclicSelection.forbidBoth_selection => Physics.DeltaBTwoCyclicSelection.forbidBoth_selection,
  GUT.DeltaBTwoCyclicSelection.forbidden_iff => Physics.DeltaBTwoCyclicSelection.forbidden_iff,
  GUT.DeltaBTwoCyclicSelection.neutral_iff => Physics.DeltaBTwoCyclicSelection.neutral_iff,
  GUT.DeltaBTwoCyclicSelection.order_one_allowed => Physics.DeltaBTwoCyclicSelection.order_one_allowed,
  GUT.DeltaBTwoCyclicSelection.quarkParity_allowed => Physics.DeltaBTwoCyclicSelection.quarkParity_allowed,
  GUT.DeltaBTwoCyclicSelection.simultaneous_forbidden_iff => Physics.DeltaBTwoCyclicSelection.simultaneous_forbidden_iff,
  GUT.DeltaBTwoCyclicSelection.simultaneous_iff => Physics.DeltaBTwoCyclicSelection.simultaneous_iff,
  GUT.DeltaBTwoCyclicSelection.trivial_allowed => Physics.DeltaBTwoCyclicSelection.trivial_allowed,
  GUT.DeltaBTwoCyclicSelection.twoProbeEquiv => Physics.DeltaBTwoCyclicSelection.twoProbeEquiv
]

assert_compatible GUT.DeltaBTwoCyclicSelection.allowed_iff => Physics.DeltaBTwoCyclicSelection.allowed_iff
assert_compatible GUT.DeltaBTwoCyclicSelection.charge => Physics.DeltaBTwoCyclicSelection.charge
assert_compatible GUT.DeltaBTwoCyclicSelection.charge.eq_1 => Physics.DeltaBTwoCyclicSelection.charge.eq_1
assert_compatible GUT.DeltaBTwoCyclicSelection.forbidBoth => Physics.DeltaBTwoCyclicSelection.forbidBoth
assert_compatible GUT.DeltaBTwoCyclicSelection.forbidBoth_conditions => Physics.DeltaBTwoCyclicSelection.forbidBoth_conditions
assert_compatible GUT.DeltaBTwoCyclicSelection.forbidBoth_selection => Physics.DeltaBTwoCyclicSelection.forbidBoth_selection
assert_compatible GUT.DeltaBTwoCyclicSelection.forbidden_iff => Physics.DeltaBTwoCyclicSelection.forbidden_iff
assert_compatible GUT.DeltaBTwoCyclicSelection.neutral_iff => Physics.DeltaBTwoCyclicSelection.neutral_iff
assert_compatible GUT.DeltaBTwoCyclicSelection.order_one_allowed => Physics.DeltaBTwoCyclicSelection.order_one_allowed
assert_compatible GUT.DeltaBTwoCyclicSelection.quarkParity_allowed => Physics.DeltaBTwoCyclicSelection.quarkParity_allowed
assert_compatible GUT.DeltaBTwoCyclicSelection.simultaneous_forbidden_iff => Physics.DeltaBTwoCyclicSelection.simultaneous_forbidden_iff
assert_compatible GUT.DeltaBTwoCyclicSelection.simultaneous_iff => Physics.DeltaBTwoCyclicSelection.simultaneous_iff
assert_compatible GUT.DeltaBTwoCyclicSelection.trivial_allowed => Physics.DeltaBTwoCyclicSelection.trivial_allowed
assert_compatible GUT.DeltaBTwoCyclicSelection.twoProbeEquiv => Physics.DeltaBTwoCyclicSelection.twoProbeEquiv
