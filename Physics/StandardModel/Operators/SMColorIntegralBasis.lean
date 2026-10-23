import Physics.StandardModel.Operators.Support.Quark.SMColorIntegralBasis
import Physics.StandardModel.Operators.SMContentWeakBound
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMColorIntegralBasis instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMColorIntegralBasis.colorWeight => Physics.SMColorIntegralBasis.colorWeight,
  GUT.SMColorIntegralBasis.colorWeight.eq_1 => Physics.SMColorIntegralBasis.colorWeight.eq_1,
  GUT.SMColorIntegralBasis.color_basis_eigen => Physics.SMColorIntegralBasis.color_basis_eigen,
  GUT.SMColorIntegralBasis.field_basis_eigen => Physics.SMColorIntegralBasis.field_basis_eigen,
  GUT.SMColorIntegralBasis.fullTorus => Physics.SMColorIntegralBasis.fullTorus,
  GUT.SMColorIntegralBasis.fullTorus.eq_1 => Physics.SMColorIntegralBasis.fullTorus.eq_1,
  GUT.SMColorIntegralBasis.gaugeTorus => Physics.SMColorIntegralBasis.gaugeTorus,
  GUT.SMColorIntegralBasis.gaugeTorus.eq_1 => Physics.SMColorIntegralBasis.gaugeTorus.eq_1,
  GUT.SMColorIntegralBasis.gaugeWeight => Physics.SMColorIntegralBasis.gaugeWeight,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_1 => Physics.SMColorIntegralBasis.gaugeWeight.eq_1,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_10 => Physics.SMColorIntegralBasis.gaugeWeight.eq_10,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_2 => Physics.SMColorIntegralBasis.gaugeWeight.eq_2,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_3 => Physics.SMColorIntegralBasis.gaugeWeight.eq_3,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_4 => Physics.SMColorIntegralBasis.gaugeWeight.eq_4,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_5 => Physics.SMColorIntegralBasis.gaugeWeight.eq_5,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_6 => Physics.SMColorIntegralBasis.gaugeWeight.eq_6,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_7 => Physics.SMColorIntegralBasis.gaugeWeight.eq_7,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_8 => Physics.SMColorIntegralBasis.gaugeWeight.eq_8,
  GUT.SMColorIntegralBasis.gaugeWeight.eq_9 => Physics.SMColorIntegralBasis.gaugeWeight.eq_9,
  GUT.SMColorIntegralBasis.gauge_basis_eigen => Physics.SMColorIntegralBasis.gauge_basis_eigen,
  GUT.SMColorIntegralBasis.instAddCommGroupPiTensorProductFinComplexFieldFlavor => Physics.SMColorIntegralBasis.instAddCommGroupPiTensorProductFinComplexFieldFlavor,
  GUT.SMColorIntegralBasis.raw_basis_eigen => Physics.SMColorIntegralBasis.raw_basis_eigen,
  GUT.SMColorIntegralBasis.raw_integral => Physics.SMColorIntegralBasis.raw_integral,
  GUT.SMColorIntegralBasis.source_integral => Physics.SMColorIntegralBasis.source_integral,
  GUT.SMColorIntegralBasis.twist_eigen => Physics.SMColorIntegralBasis.twist_eigen,
  GUT.SMColorIntegralBasis.weak_basis_eigen => Physics.SMColorIntegralBasis.weak_basis_eigen
]

assert_compatible GUT.SMColorIntegralBasis.colorWeight => Physics.SMColorIntegralBasis.colorWeight
assert_compatible GUT.SMColorIntegralBasis.colorWeight.eq_1 => Physics.SMColorIntegralBasis.colorWeight.eq_1
assert_compatible GUT.SMColorIntegralBasis.color_basis_eigen => Physics.SMColorIntegralBasis.color_basis_eigen
assert_compatible GUT.SMColorIntegralBasis.field_basis_eigen => Physics.SMColorIntegralBasis.field_basis_eigen
assert_compatible GUT.SMColorIntegralBasis.fullTorus => Physics.SMColorIntegralBasis.fullTorus
assert_compatible GUT.SMColorIntegralBasis.fullTorus.eq_1 => Physics.SMColorIntegralBasis.fullTorus.eq_1
assert_compatible GUT.SMColorIntegralBasis.gaugeTorus => Physics.SMColorIntegralBasis.gaugeTorus
assert_compatible GUT.SMColorIntegralBasis.gaugeTorus.eq_1 => Physics.SMColorIntegralBasis.gaugeTorus.eq_1
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight => Physics.SMColorIntegralBasis.gaugeWeight
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_1 => Physics.SMColorIntegralBasis.gaugeWeight.eq_1
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_10 => Physics.SMColorIntegralBasis.gaugeWeight.eq_10
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_2 => Physics.SMColorIntegralBasis.gaugeWeight.eq_2
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_3 => Physics.SMColorIntegralBasis.gaugeWeight.eq_3
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_4 => Physics.SMColorIntegralBasis.gaugeWeight.eq_4
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_5 => Physics.SMColorIntegralBasis.gaugeWeight.eq_5
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_6 => Physics.SMColorIntegralBasis.gaugeWeight.eq_6
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_7 => Physics.SMColorIntegralBasis.gaugeWeight.eq_7
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_8 => Physics.SMColorIntegralBasis.gaugeWeight.eq_8
assert_compatible GUT.SMColorIntegralBasis.gaugeWeight.eq_9 => Physics.SMColorIntegralBasis.gaugeWeight.eq_9
assert_compatible GUT.SMColorIntegralBasis.gauge_basis_eigen => Physics.SMColorIntegralBasis.gauge_basis_eigen
assert_compatible GUT.SMColorIntegralBasis.instAddCommGroupPiTensorProductFinComplexFieldFlavor => Physics.SMColorIntegralBasis.instAddCommGroupPiTensorProductFinComplexFieldFlavor
assert_compatible GUT.SMColorIntegralBasis.raw_basis_eigen => Physics.SMColorIntegralBasis.raw_basis_eigen
assert_compatible GUT.SMColorIntegralBasis.raw_integral => Physics.SMColorIntegralBasis.raw_integral
assert_compatible GUT.SMColorIntegralBasis.source_integral => Physics.SMColorIntegralBasis.source_integral
assert_compatible GUT.SMColorIntegralBasis.twist_eigen => Physics.SMColorIntegralBasis.twist_eigen
assert_compatible GUT.SMColorIntegralBasis.weak_basis_eigen => Physics.SMColorIntegralBasis.weak_basis_eigen
