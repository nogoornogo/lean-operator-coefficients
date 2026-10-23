import Physics.StandardModel.Operators.Support.Coordinates.SMConstantWeakCapacity
import Math.RepresentationTheory.BalancedExteriorWeights
import Math.RepresentationTheory.ConstantPatternExterior
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMConstantWeakCapacity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMConstantWeakCapacity.bound => Physics.SMConstantWeakCapacity.bound,
  GUT.SMConstantWeakCapacity.bound.eq_1 => Physics.SMConstantWeakCapacity.bound.eq_1,
  GUT.SMConstantWeakCapacity.dimension => Physics.SMConstantWeakCapacity.dimension,
  GUT.SMConstantWeakCapacity.dimension.eq_1 => Physics.SMConstantWeakCapacity.dimension.eq_1,
  GUT.SMConstantWeakCapacity.dimension_eq => Physics.SMConstantWeakCapacity.dimension_eq,
  GUT.SMConstantWeakCapacity.exterior_bounded => Physics.SMConstantWeakCapacity.exterior_bounded,
  GUT.SMConstantWeakCapacity.field_dimension => Physics.SMConstantWeakCapacity.field_dimension,
  GUT.SMConstantWeakCapacity.field_weight_bound => Physics.SMConstantWeakCapacity.field_weight_bound,
  GUT.SMConstantWeakCapacity.field_weight_sum => Physics.SMConstantWeakCapacity.field_weight_sum,
  GUT.SMConstantWeakCapacity.kernel_high_finrank_zero => Physics.SMConstantWeakCapacity.kernel_high_finrank_zero,
  GUT.SMConstantWeakCapacity.kernel_high_zero => Physics.SMConstantWeakCapacity.kernel_high_zero,
  GUT.SMConstantWeakCapacity.local_high_forbidden => Physics.SMConstantWeakCapacity.local_high_forbidden,
  GUT.SMConstantWeakCapacity.local_high_zero => Physics.SMConstantWeakCapacity.local_high_zero,
  GUT.SMConstantWeakCapacity.pattern => Physics.SMConstantWeakCapacity.pattern,
  GUT.SMConstantWeakCapacity.source_bounded => Physics.SMConstantWeakCapacity.source_bounded
]

assert_compatible GUT.SMConstantWeakCapacity.bound => Physics.SMConstantWeakCapacity.bound
assert_compatible GUT.SMConstantWeakCapacity.bound.eq_1 => Physics.SMConstantWeakCapacity.bound.eq_1
assert_compatible GUT.SMConstantWeakCapacity.dimension => Physics.SMConstantWeakCapacity.dimension
assert_compatible GUT.SMConstantWeakCapacity.dimension.eq_1 => Physics.SMConstantWeakCapacity.dimension.eq_1
assert_compatible GUT.SMConstantWeakCapacity.dimension_eq => Physics.SMConstantWeakCapacity.dimension_eq
assert_compatible GUT.SMConstantWeakCapacity.exterior_bounded => Physics.SMConstantWeakCapacity.exterior_bounded
assert_compatible GUT.SMConstantWeakCapacity.field_dimension => Physics.SMConstantWeakCapacity.field_dimension
assert_compatible GUT.SMConstantWeakCapacity.field_weight_bound => Physics.SMConstantWeakCapacity.field_weight_bound
assert_compatible GUT.SMConstantWeakCapacity.field_weight_sum => Physics.SMConstantWeakCapacity.field_weight_sum
assert_compatible GUT.SMConstantWeakCapacity.kernel_high_finrank_zero => Physics.SMConstantWeakCapacity.kernel_high_finrank_zero
assert_compatible GUT.SMConstantWeakCapacity.kernel_high_zero => Physics.SMConstantWeakCapacity.kernel_high_zero
assert_compatible GUT.SMConstantWeakCapacity.local_high_forbidden => Physics.SMConstantWeakCapacity.local_high_forbidden
assert_compatible GUT.SMConstantWeakCapacity.local_high_zero => Physics.SMConstantWeakCapacity.local_high_zero
assert_compatible GUT.SMConstantWeakCapacity.pattern => Physics.SMConstantWeakCapacity.pattern
assert_compatible GUT.SMConstantWeakCapacity.source_bounded => Physics.SMConstantWeakCapacity.source_bounded
