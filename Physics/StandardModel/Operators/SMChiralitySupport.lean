import Physics.StandardModel.Operators.Support.Coordinates.SMChiralitySupport
import Physics.StandardModel.Operators.SMMixedCompactWeyl
import Physics.StandardModel.Operators.SMParityKernelRank
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMChiralitySupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMChiralitySupport.action_center => Physics.SMChiralitySupport.action_center,
  GUT.SMChiralitySupport.center => Physics.SMChiralitySupport.center,
  GUT.SMChiralitySupport.center.eq_1 => Physics.SMChiralitySupport.center.eq_1,
  GUT.SMChiralitySupport.count => Physics.SMChiralitySupport.count,
  GUT.SMChiralitySupport.field_center => Physics.SMChiralitySupport.field_center,
  GUT.SMChiralitySupport.independent_fixed => Physics.SMChiralitySupport.independent_fixed,
  GUT.SMChiralitySupport.instAddCommGroupTensorProductComplex_physics => Physics.SMChiralitySupport.instAddCommGroupTensorProductComplex_physics,
  GUT.SMChiralitySupport.local_forbidden => Physics.SMChiralitySupport.local_forbidden,
  GUT.SMChiralitySupport.original_forbidden => Physics.SMChiralitySupport.original_forbidden,
  GUT.SMChiralitySupport.raw_center => Physics.SMChiralitySupport.raw_center,
  GUT.SMChiralitySupport.restrictLocal => Physics.SMChiralitySupport.restrictLocal,
  GUT.SMChiralitySupport.slotCount => Physics.SMChiralitySupport.slotCount,
  GUT.SMChiralitySupport.source_center => Physics.SMChiralitySupport.source_center,
  GUT.SMChiralitySupport.spin_center => Physics.SMChiralitySupport.spin_center,
  GUT.SMChiralitySupport.test_forbidden => Physics.SMChiralitySupport.test_forbidden
]

assert_compatible GUT.SMChiralitySupport.action_center => Physics.SMChiralitySupport.action_center
assert_compatible GUT.SMChiralitySupport.center => Physics.SMChiralitySupport.center
assert_compatible GUT.SMChiralitySupport.center.eq_1 => Physics.SMChiralitySupport.center.eq_1
assert_compatible GUT.SMChiralitySupport.count => Physics.SMChiralitySupport.count
assert_compatible GUT.SMChiralitySupport.field_center => Physics.SMChiralitySupport.field_center
assert_compatible GUT.SMChiralitySupport.independent_fixed => Physics.SMChiralitySupport.independent_fixed
assert_compatible GUT.SMChiralitySupport.instAddCommGroupTensorProductComplex_physics => Physics.SMChiralitySupport.instAddCommGroupTensorProductComplex_physics
assert_compatible GUT.SMChiralitySupport.local_forbidden => Physics.SMChiralitySupport.local_forbidden
assert_compatible GUT.SMChiralitySupport.original_forbidden => Physics.SMChiralitySupport.original_forbidden
assert_compatible GUT.SMChiralitySupport.raw_center => Physics.SMChiralitySupport.raw_center
assert_compatible GUT.SMChiralitySupport.restrictLocal => Physics.SMChiralitySupport.restrictLocal
assert_compatible GUT.SMChiralitySupport.slotCount => Physics.SMChiralitySupport.slotCount
assert_compatible GUT.SMChiralitySupport.source_center => Physics.SMChiralitySupport.source_center
assert_compatible GUT.SMChiralitySupport.spin_center => Physics.SMChiralitySupport.spin_center
assert_compatible GUT.SMChiralitySupport.test_forbidden => Physics.SMChiralitySupport.test_forbidden
