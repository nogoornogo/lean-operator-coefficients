import Physics.StandardModel.Operators.Support.Joint.SMJointWeakContent
import Physics.StandardModel.Operators.SMFiniteWeakBranching
import Math.RepresentationTheory.SU2IsotypicModels
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointWeakContent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointWeakContent.Color => Physics.SMJointWeakContent.Color,
  GUT.SMJointWeakContent.Multiplicity => Physics.SMJointWeakContent.Multiplicity,
  GUT.SMJointWeakContent.Remaining => Physics.SMJointWeakContent.Remaining,
  GUT.SMJointWeakContent.bounded => Physics.SMJointWeakContent.bounded,
  GUT.SMJointWeakContent.decomposition => Physics.SMJointWeakContent.decomposition,
  GUT.SMJointWeakContent.inverse_continuous => Physics.SMJointWeakContent.inverse_continuous,
  GUT.SMJointWeakContent.multiplicity => Physics.SMJointWeakContent.multiplicity,
  GUT.SMJointWeakContent.multiplicity_continuous => Physics.SMJointWeakContent.multiplicity_continuous,
  GUT.SMJointWeakContent.reorder => Physics.SMJointWeakContent.reorder,
  GUT.SMJointWeakContent.source => Physics.SMJointWeakContent.source,
  GUT.SMJointWeakContent.source_continuous => Physics.SMJointWeakContent.source_continuous,
  GUT.SMJointWeakContent.weak_restriction => Physics.SMJointWeakContent.weak_restriction
]

assert_compatible GUT.SMJointWeakContent.Color => Physics.SMJointWeakContent.Color
assert_compatible GUT.SMJointWeakContent.Multiplicity => Physics.SMJointWeakContent.Multiplicity
assert_compatible GUT.SMJointWeakContent.Remaining => Physics.SMJointWeakContent.Remaining
assert_compatible GUT.SMJointWeakContent.bounded => Physics.SMJointWeakContent.bounded
assert_compatible GUT.SMJointWeakContent.decomposition => Physics.SMJointWeakContent.decomposition
assert_compatible GUT.SMJointWeakContent.inverse_continuous => Physics.SMJointWeakContent.inverse_continuous
assert_compatible GUT.SMJointWeakContent.multiplicity => Physics.SMJointWeakContent.multiplicity
assert_compatible GUT.SMJointWeakContent.multiplicity_continuous => Physics.SMJointWeakContent.multiplicity_continuous
assert_compatible GUT.SMJointWeakContent.reorder => Physics.SMJointWeakContent.reorder
assert_compatible GUT.SMJointWeakContent.source => Physics.SMJointWeakContent.source
assert_compatible GUT.SMJointWeakContent.source_continuous => Physics.SMJointWeakContent.source_continuous
assert_compatible GUT.SMJointWeakContent.weak_restriction => Physics.SMJointWeakContent.weak_restriction
