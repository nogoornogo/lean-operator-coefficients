import Physics.StandardModel.Operators.Support.Decomposition.SMCompactSpinBound
import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Physics.StandardModel.Operators.SMChiralitySupport
import Math.RepresentationTheory.SubrepresentationTorusBound
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMCompactSpinBound instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMChiralitySupport.count.eq_1 => Physics.SMChiralitySupport.count.eq_1,
  GUT.SMCompactSpinBound.fieldWeight => Physics.SMCompactSpinBound.fieldWeight,
  GUT.SMCompactSpinBound.fieldWeight.eq_1 => Physics.SMCompactSpinBound.fieldWeight.eq_1,
  GUT.SMCompactSpinBound.field_bound => Physics.SMCompactSpinBound.field_bound,
  GUT.SMCompactSpinBound.field_eigen => Physics.SMCompactSpinBound.field_eigen,
  GUT.SMCompactSpinBound.model_bounded => Physics.SMCompactSpinBound.model_bounded,
  GUT.SMCompactSpinBound.raw_bounded => Physics.SMCompactSpinBound.raw_bounded,
  GUT.SMCompactSpinBound.source_bounded => Physics.SMCompactSpinBound.source_bounded,
  GUT.SMCompactSpinBound.spinTorus => Physics.SMCompactSpinBound.spinTorus,
  GUT.SMCompactSpinBound.spinTorus.eq_1 => Physics.SMCompactSpinBound.spinTorus.eq_1,
  GUT.SMCompactSpinBound.spin_eigen => Physics.SMCompactSpinBound.spin_eigen,
  GUT.SMCompactSpinBound.tensorWeight => Physics.SMCompactSpinBound.tensorWeight,
  GUT.SMCompactSpinBound.tensorWeight.eq_1 => Physics.SMCompactSpinBound.tensorWeight.eq_1,
  GUT.SMCompactSpinBound.torus => Physics.SMCompactSpinBound.torus,
  GUT.SMCompactSpinBound.weight => Physics.SMCompactSpinBound.weight,
  GUT.SMCompactSpinBound.weight.eq_1 => Physics.SMCompactSpinBound.weight.eq_1
]

assert_compatible GUT.SMChiralitySupport.count.eq_1 => Physics.SMChiralitySupport.count.eq_1
assert_compatible GUT.SMCompactSpinBound.fieldWeight => Physics.SMCompactSpinBound.fieldWeight
assert_compatible GUT.SMCompactSpinBound.fieldWeight.eq_1 => Physics.SMCompactSpinBound.fieldWeight.eq_1
assert_compatible GUT.SMCompactSpinBound.field_bound => Physics.SMCompactSpinBound.field_bound
assert_compatible GUT.SMCompactSpinBound.field_eigen => Physics.SMCompactSpinBound.field_eigen
assert_compatible GUT.SMCompactSpinBound.model_bounded => Physics.SMCompactSpinBound.model_bounded
assert_compatible GUT.SMCompactSpinBound.raw_bounded => Physics.SMCompactSpinBound.raw_bounded
assert_compatible GUT.SMCompactSpinBound.source_bounded => Physics.SMCompactSpinBound.source_bounded
assert_compatible GUT.SMCompactSpinBound.spinTorus => Physics.SMCompactSpinBound.spinTorus
assert_compatible GUT.SMCompactSpinBound.spinTorus.eq_1 => Physics.SMCompactSpinBound.spinTorus.eq_1
assert_compatible GUT.SMCompactSpinBound.spin_eigen => Physics.SMCompactSpinBound.spin_eigen
assert_compatible GUT.SMCompactSpinBound.tensorWeight => Physics.SMCompactSpinBound.tensorWeight
assert_compatible GUT.SMCompactSpinBound.tensorWeight.eq_1 => Physics.SMCompactSpinBound.tensorWeight.eq_1
assert_compatible GUT.SMCompactSpinBound.torus => Physics.SMCompactSpinBound.torus
assert_compatible GUT.SMCompactSpinBound.weight => Physics.SMCompactSpinBound.weight
assert_compatible GUT.SMCompactSpinBound.weight.eq_1 => Physics.SMCompactSpinBound.weight.eq_1
