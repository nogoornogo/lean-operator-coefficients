import Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionBounds
import Physics.StandardModel.Operators.SMB1BelowTenAssignments
import Physics.StandardModel.Operators.SMChiralitySupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionBounds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1DimensionBounds.grade_identity => Physics.SMB1DimensionBounds.grade_identity,
  GUT.SMB1DimensionBounds.lowerGrade => Physics.SMB1DimensionBounds.lowerGrade,
  GUT.SMB1DimensionBounds.original_grade_congruence => Physics.SMB1DimensionBounds.original_grade_congruence,
  GUT.SMB1DimensionBounds.original_left_even => Physics.SMB1DimensionBounds.original_left_even,
  GUT.SMB1DimensionBounds.original_lower => Physics.SMB1DimensionBounds.original_lower,
  GUT.SMB1DimensionBounds.species_grade_identity => Physics.SMB1DimensionBounds.species_grade_identity
]

assert_compatible GUT.SMB1DimensionBounds.grade_identity => Physics.SMB1DimensionBounds.grade_identity
assert_compatible GUT.SMB1DimensionBounds.lowerGrade => Physics.SMB1DimensionBounds.lowerGrade
assert_compatible GUT.SMB1DimensionBounds.original_grade_congruence => Physics.SMB1DimensionBounds.original_grade_congruence
assert_compatible GUT.SMB1DimensionBounds.original_left_even => Physics.SMB1DimensionBounds.original_left_even
assert_compatible GUT.SMB1DimensionBounds.original_lower => Physics.SMB1DimensionBounds.original_lower
assert_compatible GUT.SMB1DimensionBounds.species_grade_identity => Physics.SMB1DimensionBounds.species_grade_identity
