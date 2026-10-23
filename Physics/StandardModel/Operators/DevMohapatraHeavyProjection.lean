import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyProjection
import Physics.StandardModel.Operators.DevMohapatraHeavyAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyProjection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraHeavyElimination.constant.eq_1 => Physics.DevMohapatraHeavyElimination.constant.eq_1,
  GUT.DevMohapatraHeavyElimination.coord.eq_1 => Physics.DevMohapatraHeavyElimination.coord.eq_1,
  GUT.DevMohapatraHeavyElimination.db.eq_1 => Physics.DevMohapatraHeavyElimination.db.eq_1,
  GUT.DevMohapatraHeavyElimination.sb.eq_1 => Physics.DevMohapatraHeavyElimination.sb.eq_1,
  GUT.DevMohapatraHeavyElimination.ub.eq_1 => Physics.DevMohapatraHeavyElimination.ub.eq_1,
  GUT.DevMohapatraHeavyProjection.Light => Physics.DevMohapatraHeavyProjection.Light,
  GUT.DevMohapatraHeavyProjection.dl => Physics.DevMohapatraHeavyProjection.dl,
  GUT.DevMohapatraHeavyProjection.dl.eq_1 => Physics.DevMohapatraHeavyProjection.dl.eq_1,
  GUT.DevMohapatraHeavyProjection.holomorphicFields => Physics.DevMohapatraHeavyProjection.holomorphicFields,
  GUT.DevMohapatraHeavyProjection.holomorphicFields.eq_1 => Physics.DevMohapatraHeavyProjection.holomorphicFields.eq_1,
  GUT.DevMohapatraHeavyProjection.holomorphicFields_bar => Physics.DevMohapatraHeavyProjection.holomorphicFields_bar,
  GUT.DevMohapatraHeavyProjection.project => Physics.DevMohapatraHeavyProjection.project,
  GUT.DevMohapatraHeavyProjection.project.eq_1 => Physics.DevMohapatraHeavyProjection.project.eq_1,
  GUT.DevMohapatraHeavyProjection.project_bar_current => Physics.DevMohapatraHeavyProjection.project_bar_current,
  GUT.DevMohapatraHeavyProjection.project_bar_solution => Physics.DevMohapatraHeavyProjection.project_bar_solution,
  GUT.DevMohapatraHeavyProjection.project_constant => Physics.DevMohapatraHeavyProjection.project_constant,
  GUT.DevMohapatraHeavyProjection.project_cross => Physics.DevMohapatraHeavyProjection.project_cross,
  GUT.DevMohapatraHeavyProjection.project_current => Physics.DevMohapatraHeavyProjection.project_current,
  GUT.DevMohapatraHeavyProjection.project_eliminated_action => Physics.DevMohapatraHeavyProjection.project_eliminated_action,
  GUT.DevMohapatraHeavyProjection.project_kernel => Physics.DevMohapatraHeavyProjection.project_kernel,
  GUT.DevMohapatraHeavyProjection.project_solution_source => Physics.DevMohapatraHeavyProjection.project_solution_source,
  GUT.DevMohapatraHeavyProjection.sl => Physics.DevMohapatraHeavyProjection.sl,
  GUT.DevMohapatraHeavyProjection.sl.eq_1 => Physics.DevMohapatraHeavyProjection.sl.eq_1,
  GUT.DevMohapatraHeavyProjection.ul => Physics.DevMohapatraHeavyProjection.ul,
  GUT.DevMohapatraHeavyProjection.ul.eq_1 => Physics.DevMohapatraHeavyProjection.ul.eq_1
]

assert_compatible GUT.DevMohapatraHeavyElimination.constant.eq_1 => Physics.DevMohapatraHeavyElimination.constant.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.coord.eq_1 => Physics.DevMohapatraHeavyElimination.coord.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.db.eq_1 => Physics.DevMohapatraHeavyElimination.db.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.sb.eq_1 => Physics.DevMohapatraHeavyElimination.sb.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.ub.eq_1 => Physics.DevMohapatraHeavyElimination.ub.eq_1
assert_compatible GUT.DevMohapatraHeavyProjection.Light => Physics.DevMohapatraHeavyProjection.Light
assert_compatible GUT.DevMohapatraHeavyProjection.dl => Physics.DevMohapatraHeavyProjection.dl
assert_compatible GUT.DevMohapatraHeavyProjection.dl.eq_1 => Physics.DevMohapatraHeavyProjection.dl.eq_1
assert_compatible GUT.DevMohapatraHeavyProjection.holomorphicFields => Physics.DevMohapatraHeavyProjection.holomorphicFields
assert_compatible GUT.DevMohapatraHeavyProjection.holomorphicFields.eq_1 => Physics.DevMohapatraHeavyProjection.holomorphicFields.eq_1
assert_compatible GUT.DevMohapatraHeavyProjection.holomorphicFields_bar => Physics.DevMohapatraHeavyProjection.holomorphicFields_bar
assert_compatible GUT.DevMohapatraHeavyProjection.project => Physics.DevMohapatraHeavyProjection.project
assert_compatible GUT.DevMohapatraHeavyProjection.project.eq_1 => Physics.DevMohapatraHeavyProjection.project.eq_1
assert_compatible GUT.DevMohapatraHeavyProjection.project_bar_current => Physics.DevMohapatraHeavyProjection.project_bar_current
assert_compatible GUT.DevMohapatraHeavyProjection.project_bar_solution => Physics.DevMohapatraHeavyProjection.project_bar_solution
assert_compatible GUT.DevMohapatraHeavyProjection.project_constant => Physics.DevMohapatraHeavyProjection.project_constant
assert_compatible GUT.DevMohapatraHeavyProjection.project_cross => Physics.DevMohapatraHeavyProjection.project_cross
assert_compatible GUT.DevMohapatraHeavyProjection.project_current => Physics.DevMohapatraHeavyProjection.project_current
assert_compatible GUT.DevMohapatraHeavyProjection.project_eliminated_action => Physics.DevMohapatraHeavyProjection.project_eliminated_action
assert_compatible GUT.DevMohapatraHeavyProjection.project_kernel => Physics.DevMohapatraHeavyProjection.project_kernel
assert_compatible GUT.DevMohapatraHeavyProjection.project_solution_source => Physics.DevMohapatraHeavyProjection.project_solution_source
assert_compatible GUT.DevMohapatraHeavyProjection.sl => Physics.DevMohapatraHeavyProjection.sl
assert_compatible GUT.DevMohapatraHeavyProjection.sl.eq_1 => Physics.DevMohapatraHeavyProjection.sl.eq_1
assert_compatible GUT.DevMohapatraHeavyProjection.ul => Physics.DevMohapatraHeavyProjection.ul
assert_compatible GUT.DevMohapatraHeavyProjection.ul.eq_1 => Physics.DevMohapatraHeavyProjection.ul.eq_1
