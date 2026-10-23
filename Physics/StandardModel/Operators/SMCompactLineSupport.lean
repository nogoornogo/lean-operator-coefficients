import Physics.StandardModel.Operators.Support.Decomposition.SMCompactLineSupport
import Math.RepresentationTheory.ContinuousLineActions
import Physics.StandardModel.Operators.SMCombinedChargeSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMCompactLineSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCompactLineSupport.action_trivial => Physics.SMCompactLineSupport.action_trivial,
  GUT.SMCompactLineSupport.allowed => Physics.SMCompactLineSupport.allowed,
  GUT.SMCompactLineSupport.color => Physics.SMCompactLineSupport.color,
  GUT.SMCompactLineSupport.left => Physics.SMCompactLineSupport.left,
  GUT.SMCompactLineSupport.right => Physics.SMCompactLineSupport.right,
  GUT.SMCompactLineSupport.semisimple_action => Physics.SMCompactLineSupport.semisimple_action,
  GUT.SMCompactLineSupport.weak => Physics.SMCompactLineSupport.weak
]

assert_compatible GUT.SMCompactLineSupport.action_trivial => Physics.SMCompactLineSupport.action_trivial
assert_compatible GUT.SMCompactLineSupport.allowed => Physics.SMCompactLineSupport.allowed
assert_compatible GUT.SMCompactLineSupport.color => Physics.SMCompactLineSupport.color
assert_compatible GUT.SMCompactLineSupport.left => Physics.SMCompactLineSupport.left
assert_compatible GUT.SMCompactLineSupport.right => Physics.SMCompactLineSupport.right
assert_compatible GUT.SMCompactLineSupport.semisimple_action => Physics.SMCompactLineSupport.semisimple_action
assert_compatible GUT.SMCompactLineSupport.weak => Physics.SMCompactLineSupport.weak
