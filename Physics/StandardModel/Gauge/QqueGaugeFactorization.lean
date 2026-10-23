import Physics.StandardModel.Gauge.Tensors.QqueGaugeFactorization
import Physics.StandardModel.Gauge.QqueGaugeUniqueness
import Physics.StandardModel.Gauge.ExplicitSMResidualTensor
import Math.RepresentationTheory.ExternalInvariantFactorization
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.QqueGaugeFactorization instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueGaugeFactorization.Coefficient => Physics.QqueGaugeFactorization.Coefficient,
  GUT.QqueGaugeFactorization.instAddCommGroupQQueSpace => Physics.QqueGaugeFactorization.instAddCommGroupQQueSpace,
  GUT.QqueGaugeFactorization.instAddCommGroupQuark => Physics.QqueGaugeFactorization.instAddCommGroupQuark,
  GUT.QqueGaugeFactorization.instAddCommGroupTensorProductComplexColor => Physics.QqueGaugeFactorization.instAddCommGroupTensorProductComplexColor,
  GUT.QqueGaugeFactorization.instAddCommGroupTensorProductComplexQuark => Physics.QqueGaugeFactorization.instAddCommGroupTensorProductComplexQuark,
  GUT.QqueGaugeFactorization.reconstruct => Physics.QqueGaugeFactorization.reconstruct,
  GUT.QqueGaugeFactorization.regrouped => Physics.QqueGaugeFactorization.regrouped,
  GUT.QqueGaugeFactorization.strip => Physics.QqueGaugeFactorization.strip
]

assert_compatible GUT.QqueGaugeFactorization.Coefficient => Physics.QqueGaugeFactorization.Coefficient
assert_compatible GUT.QqueGaugeFactorization.instAddCommGroupQQueSpace => Physics.QqueGaugeFactorization.instAddCommGroupQQueSpace
assert_compatible GUT.QqueGaugeFactorization.instAddCommGroupQuark => Physics.QqueGaugeFactorization.instAddCommGroupQuark
assert_compatible GUT.QqueGaugeFactorization.instAddCommGroupTensorProductComplexColor => Physics.QqueGaugeFactorization.instAddCommGroupTensorProductComplexColor
assert_compatible GUT.QqueGaugeFactorization.instAddCommGroupTensorProductComplexQuark => Physics.QqueGaugeFactorization.instAddCommGroupTensorProductComplexQuark
assert_compatible GUT.QqueGaugeFactorization.reconstruct => Physics.QqueGaugeFactorization.reconstruct
assert_compatible GUT.QqueGaugeFactorization.regrouped => Physics.QqueGaugeFactorization.regrouped
assert_compatible GUT.QqueGaugeFactorization.strip => Physics.QqueGaugeFactorization.strip
