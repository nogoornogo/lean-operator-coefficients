import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentValues
import Physics.FieldTheory.Jets.HiggsQuarticFourMomentInvariance
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentValues instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourMomentBasis.scale.eq_1 => Physics.HiggsQuarticFourMomentBasis.scale.eq_1,
  GUT.HiggsQuarticFourMomentValues.metric_eta => Physics.HiggsQuarticFourMomentValues.metric_eta,
  GUT.HiggsQuarticFourMomentValues.native_pair_value => Physics.HiggsQuarticFourMomentValues.native_pair_value,
  GUT.HiggsQuarticFourMomentValues.pairProduct => Physics.HiggsQuarticFourMomentValues.pairProduct,
  GUT.HiggsQuarticFourMomentValues.pairProduct.eq_1 => Physics.HiggsQuarticFourMomentValues.pairProduct.eq_1,
  GUT.HiggsQuarticFourMomentValues.pair_value => Physics.HiggsQuarticFourMomentValues.pair_value,
  GUT.HiggsQuarticFourMomentValues.pair_value_trace => Physics.HiggsQuarticFourMomentValues.pair_value_trace,
  GUT.HiggsQuarticFourMomentValues.pair_word => Physics.HiggsQuarticFourMomentValues.pair_word,
  GUT.HiggsQuarticFourMomentValues.q1_value => Physics.HiggsQuarticFourMomentValues.q1_value,
  GUT.HiggsQuarticFourMomentValues.q2_value => Physics.HiggsQuarticFourMomentValues.q2_value,
  GUT.HiggsQuarticFourMomentValues.q3_value => Physics.HiggsQuarticFourMomentValues.q3_value,
  GUT.HiggsQuarticFourMomentValues.representative_value => Physics.HiggsQuarticFourMomentValues.representative_value,
  GUT.HiggsQuarticFourMomentValues.scale_factor => Physics.HiggsQuarticFourMomentValues.scale_factor,
  GUT.HiggsQuarticFourMomentValues.seven_pair => Physics.HiggsQuarticFourMomentValues.seven_pair,
  GUT.HiggsQuarticFourMomentValues.seven_value => Physics.HiggsQuarticFourMomentValues.seven_value,
  GUT.HiggsQuarticFourMomentValues.trace_channels => Physics.HiggsQuarticFourMomentValues.trace_channels,
  GUT.HiggsQuarticFourMomentValues.values => Physics.HiggsQuarticFourMomentValues.values,
  GUT.HiggsQuarticFourMomentValues.values.eq_1 => Physics.HiggsQuarticFourMomentValues.values.eq_1
]

assert_compatible GUT.HiggsQuarticFourMomentBasis.scale.eq_1 => Physics.HiggsQuarticFourMomentBasis.scale.eq_1
assert_compatible GUT.HiggsQuarticFourMomentValues.metric_eta => Physics.HiggsQuarticFourMomentValues.metric_eta
assert_compatible GUT.HiggsQuarticFourMomentValues.native_pair_value => Physics.HiggsQuarticFourMomentValues.native_pair_value
assert_compatible GUT.HiggsQuarticFourMomentValues.pairProduct => Physics.HiggsQuarticFourMomentValues.pairProduct
assert_compatible GUT.HiggsQuarticFourMomentValues.pairProduct.eq_1 => Physics.HiggsQuarticFourMomentValues.pairProduct.eq_1
assert_compatible GUT.HiggsQuarticFourMomentValues.pair_value => Physics.HiggsQuarticFourMomentValues.pair_value
assert_compatible GUT.HiggsQuarticFourMomentValues.pair_value_trace => Physics.HiggsQuarticFourMomentValues.pair_value_trace
assert_compatible GUT.HiggsQuarticFourMomentValues.pair_word => Physics.HiggsQuarticFourMomentValues.pair_word
assert_compatible GUT.HiggsQuarticFourMomentValues.q1_value => Physics.HiggsQuarticFourMomentValues.q1_value
assert_compatible GUT.HiggsQuarticFourMomentValues.q2_value => Physics.HiggsQuarticFourMomentValues.q2_value
assert_compatible GUT.HiggsQuarticFourMomentValues.q3_value => Physics.HiggsQuarticFourMomentValues.q3_value
assert_compatible GUT.HiggsQuarticFourMomentValues.representative_value => Physics.HiggsQuarticFourMomentValues.representative_value
assert_compatible GUT.HiggsQuarticFourMomentValues.scale_factor => Physics.HiggsQuarticFourMomentValues.scale_factor
assert_compatible GUT.HiggsQuarticFourMomentValues.seven_pair => Physics.HiggsQuarticFourMomentValues.seven_pair
assert_compatible GUT.HiggsQuarticFourMomentValues.seven_value => Physics.HiggsQuarticFourMomentValues.seven_value
assert_compatible GUT.HiggsQuarticFourMomentValues.trace_channels => Physics.HiggsQuarticFourMomentValues.trace_channels
assert_compatible GUT.HiggsQuarticFourMomentValues.values => Physics.HiggsQuarticFourMomentValues.values
assert_compatible GUT.HiggsQuarticFourMomentValues.values.eq_1 => Physics.HiggsQuarticFourMomentValues.values.eq_1
