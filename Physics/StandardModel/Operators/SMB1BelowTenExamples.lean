import Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTenExamples
import Physics.StandardModel.Operators.SMB1BelowTenAssignments
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTenExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1BelowTenExamples.counted_row_consumer => Physics.SMB1BelowTenExamples.counted_row_consumer,
  GUT.SMB1BelowTenExamples.dimension_nine_control => Physics.SMB1BelowTenExamples.dimension_nine_control,
  GUT.SMB1BelowTenExamples.dimension_seven_control => Physics.SMB1BelowTenExamples.dimension_seven_control,
  GUT.SMB1BelowTenExamples.dimension_six_control => Physics.SMB1BelowTenExamples.dimension_six_control,
  GUT.SMB1BelowTenExamples.negative_baryon_control => Physics.SMB1BelowTenExamples.negative_baryon_control,
  GUT.SMB1BelowTenExamples.strict_boundary_forbidden => Physics.SMB1BelowTenExamples.strict_boundary_forbidden,
  GUT.SMB1BelowTenExamples.strict_boundary_later_allowed => Physics.SMB1BelowTenExamples.strict_boundary_later_allowed,
  GUT.SMB1BelowTenExamples.strict_boundary_minimum => Physics.SMB1BelowTenExamples.strict_boundary_minimum
]

assert_compatible GUT.SMB1BelowTenExamples.counted_row_consumer => Physics.SMB1BelowTenExamples.counted_row_consumer
assert_compatible GUT.SMB1BelowTenExamples.dimension_nine_control => Physics.SMB1BelowTenExamples.dimension_nine_control
assert_compatible GUT.SMB1BelowTenExamples.dimension_seven_control => Physics.SMB1BelowTenExamples.dimension_seven_control
assert_compatible GUT.SMB1BelowTenExamples.dimension_six_control => Physics.SMB1BelowTenExamples.dimension_six_control
assert_compatible GUT.SMB1BelowTenExamples.negative_baryon_control => Physics.SMB1BelowTenExamples.negative_baryon_control
assert_compatible GUT.SMB1BelowTenExamples.strict_boundary_forbidden => Physics.SMB1BelowTenExamples.strict_boundary_forbidden
assert_compatible GUT.SMB1BelowTenExamples.strict_boundary_later_allowed => Physics.SMB1BelowTenExamples.strict_boundary_later_allowed
assert_compatible GUT.SMB1BelowTenExamples.strict_boundary_minimum => Physics.SMB1BelowTenExamples.strict_boundary_minimum
