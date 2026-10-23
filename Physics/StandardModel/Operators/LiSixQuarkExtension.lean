import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExtension
import Physics.StandardModel.Operators.SixQuarkPermutationCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkExtension instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkExtension.coefficient => Physics.LiSixQuarkExtension.coefficient,
  GUT.LiSixQuarkExtension.coefficient.eq_1 => Physics.LiSixQuarkExtension.coefficient.eq_1,
  GUT.LiSixQuarkExtension.coefficient_coordinates => Physics.LiSixQuarkExtension.coefficient_coordinates,
  GUT.LiSixQuarkExtension.coefficient_exchange => Physics.LiSixQuarkExtension.coefficient_exchange,
  GUT.LiSixQuarkExtension.coefficient_invariant => Physics.LiSixQuarkExtension.coefficient_invariant,
  GUT.LiSixQuarkExtension.coefficient_ne_zero => Physics.LiSixQuarkExtension.coefficient_ne_zero,
  GUT.LiSixQuarkExtension.extra => Physics.LiSixQuarkExtension.extra,
  GUT.LiSixQuarkExtension.extra.eq_1 => Physics.LiSixQuarkExtension.extra.eq_1,
  GUT.LiSixQuarkExtension.extraColorFirst => Physics.LiSixQuarkExtension.extraColorFirst,
  GUT.LiSixQuarkExtension.extraColorSecond => Physics.LiSixQuarkExtension.extraColorSecond,
  GUT.LiSixQuarkExtension.extraProbe => Physics.LiSixQuarkExtension.extraProbe,
  GUT.LiSixQuarkExtension.extraProbe.eq_1 => Physics.LiSixQuarkExtension.extraProbe.eq_1,
  GUT.LiSixQuarkExtension.extraProbeLinear => Physics.LiSixQuarkExtension.extraProbeLinear,
  GUT.LiSixQuarkExtension.extraProbe_extra => Physics.LiSixQuarkExtension.extraProbe_extra,
  GUT.LiSixQuarkExtension.extraProbe_transform => Physics.LiSixQuarkExtension.extraProbe_transform,
  GUT.LiSixQuarkExtension.extraProbe_word => Physics.LiSixQuarkExtension.extraProbe_word,
  GUT.LiSixQuarkExtension.extraSpinFirst => Physics.LiSixQuarkExtension.extraSpinFirst,
  GUT.LiSixQuarkExtension.extraSpinSecond => Physics.LiSixQuarkExtension.extraSpinSecond,
  GUT.LiSixQuarkExtension.extra_color_action => Physics.LiSixQuarkExtension.extra_color_action,
  GUT.LiSixQuarkExtension.extra_ne_zero => Physics.LiSixQuarkExtension.extra_ne_zero,
  GUT.LiSixQuarkExtension.extra_not_scalar_statistics => Physics.LiSixQuarkExtension.extra_not_scalar_statistics,
  GUT.LiSixQuarkExtension.extra_spin_action => Physics.LiSixQuarkExtension.extra_spin_action,
  GUT.LiSixQuarkExtension.extra_transform => Physics.LiSixQuarkExtension.extra_transform,
  GUT.LiSixQuarkExtension.localSign => Physics.LiSixQuarkExtension.localSign,
  GUT.LiSixQuarkExtension.localSign.eq_1 => Physics.LiSixQuarkExtension.localSign.eq_1,
  GUT.LiSixQuarkExtension.transform_add => Physics.LiSixQuarkExtension.transform_add,
  GUT.LiSixQuarkExtension.transform_outer => Physics.LiSixQuarkExtension.transform_outer
]

assert_compatible GUT.LiSixQuarkExtension.coefficient => Physics.LiSixQuarkExtension.coefficient
assert_compatible GUT.LiSixQuarkExtension.coefficient.eq_1 => Physics.LiSixQuarkExtension.coefficient.eq_1
assert_compatible GUT.LiSixQuarkExtension.coefficient_coordinates => Physics.LiSixQuarkExtension.coefficient_coordinates
assert_compatible GUT.LiSixQuarkExtension.coefficient_exchange => Physics.LiSixQuarkExtension.coefficient_exchange
assert_compatible GUT.LiSixQuarkExtension.coefficient_invariant => Physics.LiSixQuarkExtension.coefficient_invariant
assert_compatible GUT.LiSixQuarkExtension.coefficient_ne_zero => Physics.LiSixQuarkExtension.coefficient_ne_zero
assert_compatible GUT.LiSixQuarkExtension.extra => Physics.LiSixQuarkExtension.extra
assert_compatible GUT.LiSixQuarkExtension.extra.eq_1 => Physics.LiSixQuarkExtension.extra.eq_1
assert_compatible GUT.LiSixQuarkExtension.extraColorFirst => Physics.LiSixQuarkExtension.extraColorFirst
assert_compatible GUT.LiSixQuarkExtension.extraColorSecond => Physics.LiSixQuarkExtension.extraColorSecond
assert_compatible GUT.LiSixQuarkExtension.extraProbe => Physics.LiSixQuarkExtension.extraProbe
assert_compatible GUT.LiSixQuarkExtension.extraProbe.eq_1 => Physics.LiSixQuarkExtension.extraProbe.eq_1
assert_compatible GUT.LiSixQuarkExtension.extraProbeLinear => Physics.LiSixQuarkExtension.extraProbeLinear
assert_compatible GUT.LiSixQuarkExtension.extraProbe_extra => Physics.LiSixQuarkExtension.extraProbe_extra
assert_compatible GUT.LiSixQuarkExtension.extraProbe_transform => Physics.LiSixQuarkExtension.extraProbe_transform
assert_compatible GUT.LiSixQuarkExtension.extraProbe_word => Physics.LiSixQuarkExtension.extraProbe_word
assert_compatible GUT.LiSixQuarkExtension.extraSpinFirst => Physics.LiSixQuarkExtension.extraSpinFirst
assert_compatible GUT.LiSixQuarkExtension.extraSpinSecond => Physics.LiSixQuarkExtension.extraSpinSecond
assert_compatible GUT.LiSixQuarkExtension.extra_color_action => Physics.LiSixQuarkExtension.extra_color_action
assert_compatible GUT.LiSixQuarkExtension.extra_ne_zero => Physics.LiSixQuarkExtension.extra_ne_zero
assert_compatible GUT.LiSixQuarkExtension.extra_not_scalar_statistics => Physics.LiSixQuarkExtension.extra_not_scalar_statistics
assert_compatible GUT.LiSixQuarkExtension.extra_spin_action => Physics.LiSixQuarkExtension.extra_spin_action
assert_compatible GUT.LiSixQuarkExtension.extra_transform => Physics.LiSixQuarkExtension.extra_transform
assert_compatible GUT.LiSixQuarkExtension.localSign => Physics.LiSixQuarkExtension.localSign
assert_compatible GUT.LiSixQuarkExtension.localSign.eq_1 => Physics.LiSixQuarkExtension.localSign.eq_1
assert_compatible GUT.LiSixQuarkExtension.transform_add => Physics.LiSixQuarkExtension.transform_add
assert_compatible GUT.LiSixQuarkExtension.transform_outer => Physics.LiSixQuarkExtension.transform_outer
