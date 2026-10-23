import Physics.StandardModel.Operators.Support.Coordinates.SMContentWeakBound
import Physics.StandardModel.Operators.SMWeakWeightBasis
import Math.RepresentationTheory.PatternExteriorSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMContentWeakBound instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMContentWeakBound.bound => Physics.SMContentWeakBound.bound,
  GUT.SMContentWeakBound.bound.eq_1 => Physics.SMContentWeakBound.bound.eq_1,
  GUT.SMContentWeakBound.bound_le_degree => Physics.SMContentWeakBound.bound_le_degree,
  GUT.SMContentWeakBound.hypercharge => Physics.SMContentWeakBound.hypercharge,
  GUT.SMContentWeakBound.instAddCommGroupPiTensorProductFinComplexFieldFlavor => Physics.SMContentWeakBound.instAddCommGroupPiTensorProductFinComplexFieldFlavor,
  GUT.SMContentWeakBound.pilot => Physics.SMContentWeakBound.pilot,
  GUT.SMContentWeakBound.pilot_bound => Physics.SMContentWeakBound.pilot_bound,
  GUT.SMContentWeakBound.raw_bounded => Physics.SMContentWeakBound.raw_bounded,
  GUT.SMContentWeakBound.raw_hypercharge => Physics.SMContentWeakBound.raw_hypercharge,
  GUT.SMContentWeakBound.source => Physics.SMContentWeakBound.source,
  GUT.SMContentWeakBound.source_bounded => Physics.SMContentWeakBound.source_bounded,
  GUT.SMContentWeakBound.source_dual_eigen_zero => Physics.SMContentWeakBound.source_dual_eigen_zero,
  GUT.SMContentWeakBound.source_hypercharge => Physics.SMContentWeakBound.source_hypercharge,
  GUT.SMContentWeakBound.tensorBasis => Physics.SMContentWeakBound.tensorBasis,
  GUT.SMContentWeakBound.tensorBasis.eq_1 => Physics.SMContentWeakBound.tensorBasis.eq_1,
  GUT.SMContentWeakBound.tensorWeight => Physics.SMContentWeakBound.tensorWeight,
  GUT.SMContentWeakBound.tensorWeight.eq_1 => Physics.SMContentWeakBound.tensorWeight.eq_1,
  GUT.SMContentWeakBound.tensor_basis_eigen => Physics.SMContentWeakBound.tensor_basis_eigen,
  GUT.SMContentWeakBound.tensor_weight_bound => Physics.SMContentWeakBound.tensor_weight_bound
]

assert_compatible GUT.SMContentWeakBound.bound => Physics.SMContentWeakBound.bound
assert_compatible GUT.SMContentWeakBound.bound.eq_1 => Physics.SMContentWeakBound.bound.eq_1
assert_compatible GUT.SMContentWeakBound.bound_le_degree => Physics.SMContentWeakBound.bound_le_degree
assert_compatible GUT.SMContentWeakBound.hypercharge => Physics.SMContentWeakBound.hypercharge
assert_compatible GUT.SMContentWeakBound.instAddCommGroupPiTensorProductFinComplexFieldFlavor => Physics.SMContentWeakBound.instAddCommGroupPiTensorProductFinComplexFieldFlavor
assert_compatible GUT.SMContentWeakBound.pilot => Physics.SMContentWeakBound.pilot
assert_compatible GUT.SMContentWeakBound.pilot_bound => Physics.SMContentWeakBound.pilot_bound
assert_compatible GUT.SMContentWeakBound.raw_bounded => Physics.SMContentWeakBound.raw_bounded
assert_compatible GUT.SMContentWeakBound.raw_hypercharge => Physics.SMContentWeakBound.raw_hypercharge
assert_compatible GUT.SMContentWeakBound.source => Physics.SMContentWeakBound.source
assert_compatible GUT.SMContentWeakBound.source_bounded => Physics.SMContentWeakBound.source_bounded
assert_compatible GUT.SMContentWeakBound.source_dual_eigen_zero => Physics.SMContentWeakBound.source_dual_eigen_zero
assert_compatible GUT.SMContentWeakBound.source_hypercharge => Physics.SMContentWeakBound.source_hypercharge
assert_compatible GUT.SMContentWeakBound.tensorBasis => Physics.SMContentWeakBound.tensorBasis
assert_compatible GUT.SMContentWeakBound.tensorBasis.eq_1 => Physics.SMContentWeakBound.tensorBasis.eq_1
assert_compatible GUT.SMContentWeakBound.tensorWeight => Physics.SMContentWeakBound.tensorWeight
assert_compatible GUT.SMContentWeakBound.tensorWeight.eq_1 => Physics.SMContentWeakBound.tensorWeight.eq_1
assert_compatible GUT.SMContentWeakBound.tensor_basis_eigen => Physics.SMContentWeakBound.tensor_basis_eigen
assert_compatible GUT.SMContentWeakBound.tensor_weight_bound => Physics.SMContentWeakBound.tensor_weight_bound
