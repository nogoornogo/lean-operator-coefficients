import Physics.StandardModel.Operators.Support.Dimension.SMB1StrongDimensionBounds
import Physics.StandardModel.Operators.SMB1WeakDimensionBounds
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1StrongDimensionBounds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1StrongDimensionBounds.lowerGrade => Physics.SMB1StrongDimensionBounds.lowerGrade,
  GUT.SMB1StrongDimensionBounds.lowerGrade.eq_1 => Physics.SMB1StrongDimensionBounds.lowerGrade.eq_1,
  GUT.SMB1StrongDimensionBounds.original_lower => Physics.SMB1StrongDimensionBounds.original_lower,
  GUT.SMB1StrongDimensionBounds.rawLower => Physics.SMB1StrongDimensionBounds.rawLower,
  GUT.SMB1StrongDimensionBounds.rawLower.eq_1 => Physics.SMB1StrongDimensionBounds.rawLower.eq_1
]

assert_compatible GUT.SMB1StrongDimensionBounds.lowerGrade => Physics.SMB1StrongDimensionBounds.lowerGrade
assert_compatible GUT.SMB1StrongDimensionBounds.lowerGrade.eq_1 => Physics.SMB1StrongDimensionBounds.lowerGrade.eq_1
assert_compatible GUT.SMB1StrongDimensionBounds.original_lower => Physics.SMB1StrongDimensionBounds.original_lower
assert_compatible GUT.SMB1StrongDimensionBounds.rawLower => Physics.SMB1StrongDimensionBounds.rawLower
assert_compatible GUT.SMB1StrongDimensionBounds.rawLower.eq_1 => Physics.SMB1StrongDimensionBounds.rawLower.eq_1
