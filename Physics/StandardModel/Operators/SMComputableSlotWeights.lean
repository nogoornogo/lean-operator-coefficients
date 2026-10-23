import Physics.StandardModel.Operators.Support.Decomposition.SMComputableSlotWeights
import Physics.StandardModel.Operators.SMCompactTorus
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMComputableSlotWeights instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCompactTorus.monomial.eq_1 => Physics.SMCompactTorus.monomial.eq_1,
  GUT.SMComputableSlotWeights.colorWeight => Physics.SMComputableSlotWeights.colorWeight,
  GUT.SMComputableSlotWeights.colorWeight.eq_1 => Physics.SMComputableSlotWeights.colorWeight.eq_1,
  GUT.SMComputableSlotWeights.color_eigen => Physics.SMComputableSlotWeights.color_eigen,
  GUT.SMComputableSlotWeights.dual_eigen => Physics.SMComputableSlotWeights.dual_eigen,
  GUT.SMComputableSlotWeights.fieldWeight => Physics.SMComputableSlotWeights.fieldWeight,
  GUT.SMComputableSlotWeights.fieldWeight.eq_1 => Physics.SMComputableSlotWeights.fieldWeight.eq_1,
  GUT.SMComputableSlotWeights.field_eigen => Physics.SMComputableSlotWeights.field_eigen,
  GUT.SMComputableSlotWeights.gaugeTorus => Physics.SMComputableSlotWeights.gaugeTorus,
  GUT.SMComputableSlotWeights.gaugeWeight => Physics.SMComputableSlotWeights.gaugeWeight,
  GUT.SMComputableSlotWeights.gauge_eigen => Physics.SMComputableSlotWeights.gauge_eigen,
  GUT.SMComputableSlotWeights.hyperWeight => Physics.SMComputableSlotWeights.hyperWeight,
  GUT.SMComputableSlotWeights.hyperWeight.eq_1 => Physics.SMComputableSlotWeights.hyperWeight.eq_1,
  GUT.SMComputableSlotWeights.monomial_add => Physics.SMComputableSlotWeights.monomial_add,
  GUT.SMComputableSlotWeights.monomial_color => Physics.SMComputableSlotWeights.monomial_color,
  GUT.SMComputableSlotWeights.monomial_hyper => Physics.SMComputableSlotWeights.monomial_hyper,
  GUT.SMComputableSlotWeights.monomial_inverse => Physics.SMComputableSlotWeights.monomial_inverse,
  GUT.SMComputableSlotWeights.monomial_weak => Physics.SMComputableSlotWeights.monomial_weak,
  GUT.SMComputableSlotWeights.monomial_zero => Physics.SMComputableSlotWeights.monomial_zero,
  GUT.SMComputableSlotWeights.spinWeight => Physics.SMComputableSlotWeights.spinWeight,
  GUT.SMComputableSlotWeights.spinWeight.eq_1 => Physics.SMComputableSlotWeights.spinWeight.eq_1,
  GUT.SMComputableSlotWeights.spin_eigen => Physics.SMComputableSlotWeights.spin_eigen,
  GUT.SMComputableSlotWeights.tensor_eigen => Physics.SMComputableSlotWeights.tensor_eigen,
  GUT.SMComputableSlotWeights.twist_eigen => Physics.SMComputableSlotWeights.twist_eigen,
  GUT.SMComputableSlotWeights.weakWeightVector => Physics.SMComputableSlotWeights.weakWeightVector,
  GUT.SMComputableSlotWeights.weakWeightVector.eq_1 => Physics.SMComputableSlotWeights.weakWeightVector.eq_1,
  GUT.SMComputableSlotWeights.weak_eigen => Physics.SMComputableSlotWeights.weak_eigen
]

assert_compatible GUT.SMCompactTorus.monomial.eq_1 => Physics.SMCompactTorus.monomial.eq_1
assert_compatible GUT.SMComputableSlotWeights.colorWeight => Physics.SMComputableSlotWeights.colorWeight
assert_compatible GUT.SMComputableSlotWeights.colorWeight.eq_1 => Physics.SMComputableSlotWeights.colorWeight.eq_1
assert_compatible GUT.SMComputableSlotWeights.color_eigen => Physics.SMComputableSlotWeights.color_eigen
assert_compatible GUT.SMComputableSlotWeights.dual_eigen => Physics.SMComputableSlotWeights.dual_eigen
assert_compatible GUT.SMComputableSlotWeights.fieldWeight => Physics.SMComputableSlotWeights.fieldWeight
assert_compatible GUT.SMComputableSlotWeights.fieldWeight.eq_1 => Physics.SMComputableSlotWeights.fieldWeight.eq_1
assert_compatible GUT.SMComputableSlotWeights.field_eigen => Physics.SMComputableSlotWeights.field_eigen
assert_compatible GUT.SMComputableSlotWeights.gaugeTorus => Physics.SMComputableSlotWeights.gaugeTorus
assert_compatible GUT.SMComputableSlotWeights.gaugeWeight => Physics.SMComputableSlotWeights.gaugeWeight
assert_compatible GUT.SMComputableSlotWeights.gauge_eigen => Physics.SMComputableSlotWeights.gauge_eigen
assert_compatible GUT.SMComputableSlotWeights.hyperWeight => Physics.SMComputableSlotWeights.hyperWeight
assert_compatible GUT.SMComputableSlotWeights.hyperWeight.eq_1 => Physics.SMComputableSlotWeights.hyperWeight.eq_1
assert_compatible GUT.SMComputableSlotWeights.monomial_add => Physics.SMComputableSlotWeights.monomial_add
assert_compatible GUT.SMComputableSlotWeights.monomial_color => Physics.SMComputableSlotWeights.monomial_color
assert_compatible GUT.SMComputableSlotWeights.monomial_hyper => Physics.SMComputableSlotWeights.monomial_hyper
assert_compatible GUT.SMComputableSlotWeights.monomial_inverse => Physics.SMComputableSlotWeights.monomial_inverse
assert_compatible GUT.SMComputableSlotWeights.monomial_weak => Physics.SMComputableSlotWeights.monomial_weak
assert_compatible GUT.SMComputableSlotWeights.monomial_zero => Physics.SMComputableSlotWeights.monomial_zero
assert_compatible GUT.SMComputableSlotWeights.spinWeight => Physics.SMComputableSlotWeights.spinWeight
assert_compatible GUT.SMComputableSlotWeights.spinWeight.eq_1 => Physics.SMComputableSlotWeights.spinWeight.eq_1
assert_compatible GUT.SMComputableSlotWeights.spin_eigen => Physics.SMComputableSlotWeights.spin_eigen
assert_compatible GUT.SMComputableSlotWeights.tensor_eigen => Physics.SMComputableSlotWeights.tensor_eigen
assert_compatible GUT.SMComputableSlotWeights.twist_eigen => Physics.SMComputableSlotWeights.twist_eigen
assert_compatible GUT.SMComputableSlotWeights.weakWeightVector => Physics.SMComputableSlotWeights.weakWeightVector
assert_compatible GUT.SMComputableSlotWeights.weakWeightVector.eq_1 => Physics.SMComputableSlotWeights.weakWeightVector.eq_1
assert_compatible GUT.SMComputableSlotWeights.weak_eigen => Physics.SMComputableSlotWeights.weak_eigen
