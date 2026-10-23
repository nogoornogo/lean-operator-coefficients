import Physics.StandardModel.Operators.Support.Coordinates.SMWeakWeightBasis
import Math.RepresentationTheory.BoundedTorusWeights
import Physics.StandardModel.Operators.WeakSingletHiggsSupport
import Physics.StandardModel.Operators.ThreeGenerationFermionBound
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMWeakWeightBasis instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMWeakWeightBasis.FieldIndex => Physics.SMWeakWeightBasis.FieldIndex,
  GUT.SMWeakWeightBasis.GaugeIndex => Physics.SMWeakWeightBasis.GaugeIndex,
  GUT.SMWeakWeightBasis.color_basis_eigen => Physics.SMWeakWeightBasis.color_basis_eigen,
  GUT.SMWeakWeightBasis.doubletCount => Physics.SMWeakWeightBasis.doubletCount,
  GUT.SMWeakWeightBasis.doubletCount.eq_1 => Physics.SMWeakWeightBasis.doubletCount.eq_1,
  GUT.SMWeakWeightBasis.fieldBasis => Physics.SMWeakWeightBasis.fieldBasis,
  GUT.SMWeakWeightBasis.fieldBasis.eq_1 => Physics.SMWeakWeightBasis.fieldBasis.eq_1,
  GUT.SMWeakWeightBasis.field_basis_eigen => Physics.SMWeakWeightBasis.field_basis_eigen,
  GUT.SMWeakWeightBasis.field_bounded => Physics.SMWeakWeightBasis.field_bounded,
  GUT.SMWeakWeightBasis.fullTorus => Physics.SMWeakWeightBasis.fullTorus,
  GUT.SMWeakWeightBasis.fullTorus.eq_1 => Physics.SMWeakWeightBasis.fullTorus.eq_1,
  GUT.SMWeakWeightBasis.gaugeBasis => Physics.SMWeakWeightBasis.gaugeBasis,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_1 => Physics.SMWeakWeightBasis.gaugeBasis.eq_1,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_10 => Physics.SMWeakWeightBasis.gaugeBasis.eq_10,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_2 => Physics.SMWeakWeightBasis.gaugeBasis.eq_2,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_3 => Physics.SMWeakWeightBasis.gaugeBasis.eq_3,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_4 => Physics.SMWeakWeightBasis.gaugeBasis.eq_4,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_5 => Physics.SMWeakWeightBasis.gaugeBasis.eq_5,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_6 => Physics.SMWeakWeightBasis.gaugeBasis.eq_6,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_7 => Physics.SMWeakWeightBasis.gaugeBasis.eq_7,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_8 => Physics.SMWeakWeightBasis.gaugeBasis.eq_8,
  GUT.SMWeakWeightBasis.gaugeBasis.eq_9 => Physics.SMWeakWeightBasis.gaugeBasis.eq_9,
  GUT.SMWeakWeightBasis.gaugeTorus => Physics.SMWeakWeightBasis.gaugeTorus,
  GUT.SMWeakWeightBasis.gaugeTorus.eq_1 => Physics.SMWeakWeightBasis.gaugeTorus.eq_1,
  GUT.SMWeakWeightBasis.gaugeWeight => Physics.SMWeakWeightBasis.gaugeWeight,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_1 => Physics.SMWeakWeightBasis.gaugeWeight.eq_1,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_10 => Physics.SMWeakWeightBasis.gaugeWeight.eq_10,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_2 => Physics.SMWeakWeightBasis.gaugeWeight.eq_2,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_3 => Physics.SMWeakWeightBasis.gaugeWeight.eq_3,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_4 => Physics.SMWeakWeightBasis.gaugeWeight.eq_4,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_5 => Physics.SMWeakWeightBasis.gaugeWeight.eq_5,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_6 => Physics.SMWeakWeightBasis.gaugeWeight.eq_6,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_7 => Physics.SMWeakWeightBasis.gaugeWeight.eq_7,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_8 => Physics.SMWeakWeightBasis.gaugeWeight.eq_8,
  GUT.SMWeakWeightBasis.gaugeWeight.eq_9 => Physics.SMWeakWeightBasis.gaugeWeight.eq_9,
  GUT.SMWeakWeightBasis.gauge_basis_eigen => Physics.SMWeakWeightBasis.gauge_basis_eigen,
  GUT.SMWeakWeightBasis.gauge_weight_bound => Physics.SMWeakWeightBasis.gauge_weight_bound,
  GUT.SMWeakWeightBasis.instDecidableEqGaugeIndex => Physics.SMWeakWeightBasis.instDecidableEqGaugeIndex,
  GUT.SMWeakWeightBasis.instFintypeGaugeIndex => Physics.SMWeakWeightBasis.instFintypeGaugeIndex,
  GUT.SMWeakWeightBasis.quarkBasis => Physics.SMWeakWeightBasis.quarkBasis,
  GUT.SMWeakWeightBasis.quarkBasis.eq_1 => Physics.SMWeakWeightBasis.quarkBasis.eq_1,
  GUT.SMWeakWeightBasis.scalarBasis => Physics.SMWeakWeightBasis.scalarBasis,
  GUT.SMWeakWeightBasis.twist_eigen => Physics.SMWeakWeightBasis.twist_eigen,
  GUT.SMWeakWeightBasis.weakWeight => Physics.SMWeakWeightBasis.weakWeight,
  GUT.SMWeakWeightBasis.weakWeight.eq_1 => Physics.SMWeakWeightBasis.weakWeight.eq_1,
  GUT.SMWeakWeightBasis.weak_basis_eigen => Physics.SMWeakWeightBasis.weak_basis_eigen,
  GUT.WeakSingletHiggsSupport.weakInclusion.eq_1 => Physics.WeakSingletHiggsSupport.weakInclusion.eq_1
]

assert_compatible GUT.SMWeakWeightBasis.FieldIndex => Physics.SMWeakWeightBasis.FieldIndex
assert_compatible GUT.SMWeakWeightBasis.GaugeIndex => Physics.SMWeakWeightBasis.GaugeIndex
assert_compatible GUT.SMWeakWeightBasis.color_basis_eigen => Physics.SMWeakWeightBasis.color_basis_eigen
assert_compatible GUT.SMWeakWeightBasis.doubletCount => Physics.SMWeakWeightBasis.doubletCount
assert_compatible GUT.SMWeakWeightBasis.doubletCount.eq_1 => Physics.SMWeakWeightBasis.doubletCount.eq_1
assert_compatible GUT.SMWeakWeightBasis.fieldBasis => Physics.SMWeakWeightBasis.fieldBasis
assert_compatible GUT.SMWeakWeightBasis.fieldBasis.eq_1 => Physics.SMWeakWeightBasis.fieldBasis.eq_1
assert_compatible GUT.SMWeakWeightBasis.field_basis_eigen => Physics.SMWeakWeightBasis.field_basis_eigen
assert_compatible GUT.SMWeakWeightBasis.field_bounded => Physics.SMWeakWeightBasis.field_bounded
assert_compatible GUT.SMWeakWeightBasis.fullTorus => Physics.SMWeakWeightBasis.fullTorus
assert_compatible GUT.SMWeakWeightBasis.fullTorus.eq_1 => Physics.SMWeakWeightBasis.fullTorus.eq_1
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis => Physics.SMWeakWeightBasis.gaugeBasis
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_1 => Physics.SMWeakWeightBasis.gaugeBasis.eq_1
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_10 => Physics.SMWeakWeightBasis.gaugeBasis.eq_10
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_2 => Physics.SMWeakWeightBasis.gaugeBasis.eq_2
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_3 => Physics.SMWeakWeightBasis.gaugeBasis.eq_3
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_4 => Physics.SMWeakWeightBasis.gaugeBasis.eq_4
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_5 => Physics.SMWeakWeightBasis.gaugeBasis.eq_5
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_6 => Physics.SMWeakWeightBasis.gaugeBasis.eq_6
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_7 => Physics.SMWeakWeightBasis.gaugeBasis.eq_7
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_8 => Physics.SMWeakWeightBasis.gaugeBasis.eq_8
assert_compatible GUT.SMWeakWeightBasis.gaugeBasis.eq_9 => Physics.SMWeakWeightBasis.gaugeBasis.eq_9
assert_compatible GUT.SMWeakWeightBasis.gaugeTorus => Physics.SMWeakWeightBasis.gaugeTorus
assert_compatible GUT.SMWeakWeightBasis.gaugeTorus.eq_1 => Physics.SMWeakWeightBasis.gaugeTorus.eq_1
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight => Physics.SMWeakWeightBasis.gaugeWeight
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_1 => Physics.SMWeakWeightBasis.gaugeWeight.eq_1
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_10 => Physics.SMWeakWeightBasis.gaugeWeight.eq_10
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_2 => Physics.SMWeakWeightBasis.gaugeWeight.eq_2
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_3 => Physics.SMWeakWeightBasis.gaugeWeight.eq_3
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_4 => Physics.SMWeakWeightBasis.gaugeWeight.eq_4
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_5 => Physics.SMWeakWeightBasis.gaugeWeight.eq_5
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_6 => Physics.SMWeakWeightBasis.gaugeWeight.eq_6
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_7 => Physics.SMWeakWeightBasis.gaugeWeight.eq_7
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_8 => Physics.SMWeakWeightBasis.gaugeWeight.eq_8
assert_compatible GUT.SMWeakWeightBasis.gaugeWeight.eq_9 => Physics.SMWeakWeightBasis.gaugeWeight.eq_9
assert_compatible GUT.SMWeakWeightBasis.gauge_basis_eigen => Physics.SMWeakWeightBasis.gauge_basis_eigen
assert_compatible GUT.SMWeakWeightBasis.gauge_weight_bound => Physics.SMWeakWeightBasis.gauge_weight_bound
assert_compatible GUT.SMWeakWeightBasis.instDecidableEqGaugeIndex => Physics.SMWeakWeightBasis.instDecidableEqGaugeIndex
assert_compatible GUT.SMWeakWeightBasis.instFintypeGaugeIndex => Physics.SMWeakWeightBasis.instFintypeGaugeIndex
assert_compatible GUT.SMWeakWeightBasis.quarkBasis => Physics.SMWeakWeightBasis.quarkBasis
assert_compatible GUT.SMWeakWeightBasis.quarkBasis.eq_1 => Physics.SMWeakWeightBasis.quarkBasis.eq_1
assert_compatible GUT.SMWeakWeightBasis.scalarBasis => Physics.SMWeakWeightBasis.scalarBasis
assert_compatible GUT.SMWeakWeightBasis.twist_eigen => Physics.SMWeakWeightBasis.twist_eigen
assert_compatible GUT.SMWeakWeightBasis.weakWeight => Physics.SMWeakWeightBasis.weakWeight
assert_compatible GUT.SMWeakWeightBasis.weakWeight.eq_1 => Physics.SMWeakWeightBasis.weakWeight.eq_1
assert_compatible GUT.SMWeakWeightBasis.weak_basis_eigen => Physics.SMWeakWeightBasis.weak_basis_eigen
assert_compatible GUT.WeakSingletHiggsSupport.weakInclusion.eq_1 => Physics.WeakSingletHiggsSupport.weakInclusion.eq_1
