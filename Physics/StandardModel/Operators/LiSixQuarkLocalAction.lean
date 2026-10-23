import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalAction
import Physics.StandardModel.Operators.SixQuarkSpeciesQuotient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkLocalAction.Arr => Physics.LiSixQuarkLocalAction.Arr,
  GUT.LiSixQuarkLocalAction.Vec => Physics.LiSixQuarkLocalAction.Vec,
  GUT.LiSixQuarkLocalAction.action => Physics.LiSixQuarkLocalAction.action,
  GUT.LiSixQuarkLocalAction.action_actual => Physics.LiSixQuarkLocalAction.action_actual,
  GUT.LiSixQuarkLocalAction.color => Physics.LiSixQuarkLocalAction.color,
  GUT.LiSixQuarkLocalAction.color.eq_1 => Physics.LiSixQuarkLocalAction.color.eq_1,
  GUT.LiSixQuarkLocalAction.color.eq_2 => Physics.LiSixQuarkLocalAction.color.eq_2,
  GUT.LiSixQuarkLocalAction.color.eq_3 => Physics.LiSixQuarkLocalAction.color.eq_3,
  GUT.LiSixQuarkLocalAction.color.eq_4 => Physics.LiSixQuarkLocalAction.color.eq_4,
  GUT.LiSixQuarkLocalAction.colorLinear => Physics.LiSixQuarkLocalAction.colorLinear,
  GUT.LiSixQuarkLocalAction.color_actual => Physics.LiSixQuarkLocalAction.color_actual,
  GUT.LiSixQuarkLocalAction.column => Physics.LiSixQuarkLocalAction.column,
  GUT.LiSixQuarkLocalAction.column_outer => Physics.LiSixQuarkLocalAction.column_outer,
  GUT.LiSixQuarkLocalAction.row => Physics.LiSixQuarkLocalAction.row,
  GUT.LiSixQuarkLocalAction.row_outer => Physics.LiSixQuarkLocalAction.row_outer,
  GUT.LiSixQuarkLocalAction.spin => Physics.LiSixQuarkLocalAction.spin,
  GUT.LiSixQuarkLocalAction.spin.eq_1 => Physics.LiSixQuarkLocalAction.spin.eq_1,
  GUT.LiSixQuarkLocalAction.spin.eq_2 => Physics.LiSixQuarkLocalAction.spin.eq_2,
  GUT.LiSixQuarkLocalAction.spin.eq_3 => Physics.LiSixQuarkLocalAction.spin.eq_3,
  GUT.LiSixQuarkLocalAction.spin.eq_4 => Physics.LiSixQuarkLocalAction.spin.eq_4,
  GUT.LiSixQuarkLocalAction.spinLinear => Physics.LiSixQuarkLocalAction.spinLinear,
  GUT.LiSixQuarkLocalAction.spin_actual => Physics.LiSixQuarkLocalAction.spin_actual
]

assert_compatible GUT.LiSixQuarkLocalAction.Arr => Physics.LiSixQuarkLocalAction.Arr
assert_compatible GUT.LiSixQuarkLocalAction.Vec => Physics.LiSixQuarkLocalAction.Vec
assert_compatible GUT.LiSixQuarkLocalAction.action => Physics.LiSixQuarkLocalAction.action
assert_compatible GUT.LiSixQuarkLocalAction.action_actual => Physics.LiSixQuarkLocalAction.action_actual
assert_compatible GUT.LiSixQuarkLocalAction.color => Physics.LiSixQuarkLocalAction.color
assert_compatible GUT.LiSixQuarkLocalAction.color.eq_1 => Physics.LiSixQuarkLocalAction.color.eq_1
assert_compatible GUT.LiSixQuarkLocalAction.color.eq_2 => Physics.LiSixQuarkLocalAction.color.eq_2
assert_compatible GUT.LiSixQuarkLocalAction.color.eq_3 => Physics.LiSixQuarkLocalAction.color.eq_3
assert_compatible GUT.LiSixQuarkLocalAction.color.eq_4 => Physics.LiSixQuarkLocalAction.color.eq_4
assert_compatible GUT.LiSixQuarkLocalAction.colorLinear => Physics.LiSixQuarkLocalAction.colorLinear
assert_compatible GUT.LiSixQuarkLocalAction.color_actual => Physics.LiSixQuarkLocalAction.color_actual
assert_compatible GUT.LiSixQuarkLocalAction.column => Physics.LiSixQuarkLocalAction.column
assert_compatible GUT.LiSixQuarkLocalAction.column_outer => Physics.LiSixQuarkLocalAction.column_outer
assert_compatible GUT.LiSixQuarkLocalAction.row => Physics.LiSixQuarkLocalAction.row
assert_compatible GUT.LiSixQuarkLocalAction.row_outer => Physics.LiSixQuarkLocalAction.row_outer
assert_compatible GUT.LiSixQuarkLocalAction.spin => Physics.LiSixQuarkLocalAction.spin
assert_compatible GUT.LiSixQuarkLocalAction.spin.eq_1 => Physics.LiSixQuarkLocalAction.spin.eq_1
assert_compatible GUT.LiSixQuarkLocalAction.spin.eq_2 => Physics.LiSixQuarkLocalAction.spin.eq_2
assert_compatible GUT.LiSixQuarkLocalAction.spin.eq_3 => Physics.LiSixQuarkLocalAction.spin.eq_3
assert_compatible GUT.LiSixQuarkLocalAction.spin.eq_4 => Physics.LiSixQuarkLocalAction.spin.eq_4
assert_compatible GUT.LiSixQuarkLocalAction.spinLinear => Physics.LiSixQuarkLocalAction.spinLinear
assert_compatible GUT.LiSixQuarkLocalAction.spin_actual => Physics.LiSixQuarkLocalAction.spin_actual
