import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyElimination
import Physics.StandardModel.Operators.DevMohapatraHermitian
import Math.LinearAlgebra.ExteriorNilpotentKernel
import Math.LinearAlgebra.ExteriorOdd
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyElimination instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraHeavyElimination.R => Physics.DevMohapatraHeavyElimination.R,
  GUT.DevMohapatraHeavyElimination.V => Physics.DevMohapatraHeavyElimination.V,
  GUT.DevMohapatraHeavyElimination.action => Physics.DevMohapatraHeavyElimination.action,
  GUT.DevMohapatraHeavyElimination.action.eq_1 => Physics.DevMohapatraHeavyElimination.action.eq_1,
  GUT.DevMohapatraHeavyElimination.constant => Physics.DevMohapatraHeavyElimination.constant,
  GUT.DevMohapatraHeavyElimination.coord => Physics.DevMohapatraHeavyElimination.coord,
  GUT.DevMohapatraHeavyElimination.cross => Physics.DevMohapatraHeavyElimination.cross,
  GUT.DevMohapatraHeavyElimination.cross.eq_1 => Physics.DevMohapatraHeavyElimination.cross.eq_1,
  GUT.DevMohapatraHeavyElimination.cross_commutes => Physics.DevMohapatraHeavyElimination.cross_commutes,
  GUT.DevMohapatraHeavyElimination.cross_degree => Physics.DevMohapatraHeavyElimination.cross_degree,
  GUT.DevMohapatraHeavyElimination.cross_even => Physics.DevMohapatraHeavyElimination.cross_even,
  GUT.DevMohapatraHeavyElimination.current_odd => Physics.DevMohapatraHeavyElimination.current_odd,
  GUT.DevMohapatraHeavyElimination.d => Physics.DevMohapatraHeavyElimination.d,
  GUT.DevMohapatraHeavyElimination.db => Physics.DevMohapatraHeavyElimination.db,
  GUT.DevMohapatraHeavyElimination.eliminated_action => Physics.DevMohapatraHeavyElimination.eliminated_action,
  GUT.DevMohapatraHeavyElimination.euler => Physics.DevMohapatraHeavyElimination.euler,
  GUT.DevMohapatraHeavyElimination.kernel => Physics.DevMohapatraHeavyElimination.kernel,
  GUT.DevMohapatraHeavyElimination.kernel.eq_1 => Physics.DevMohapatraHeavyElimination.kernel.eq_1,
  GUT.DevMohapatraHeavyElimination.kernel_degree => Physics.DevMohapatraHeavyElimination.kernel_degree,
  GUT.DevMohapatraHeavyElimination.kernel_even => Physics.DevMohapatraHeavyElimination.kernel_even,
  GUT.DevMohapatraHeavyElimination.kernel_nilpotent => Physics.DevMohapatraHeavyElimination.kernel_nilpotent,
  GUT.DevMohapatraHeavyElimination.kernel_preserves_odd => Physics.DevMohapatraHeavyElimination.kernel_preserves_odd,
  GUT.DevMohapatraHeavyElimination.linear => Physics.DevMohapatraHeavyElimination.linear,
  GUT.DevMohapatraHeavyElimination.linear.eq_1 => Physics.DevMohapatraHeavyElimination.linear.eq_1,
  GUT.DevMohapatraHeavyElimination.quadratic => Physics.DevMohapatraHeavyElimination.quadratic,
  GUT.DevMohapatraHeavyElimination.quadratic.eq_1 => Physics.DevMohapatraHeavyElimination.quadratic.eq_1,
  GUT.DevMohapatraHeavyElimination.residual => Physics.DevMohapatraHeavyElimination.residual,
  GUT.DevMohapatraHeavyElimination.residual.eq_1 => Physics.DevMohapatraHeavyElimination.residual.eq_1,
  GUT.DevMohapatraHeavyElimination.residual_factor => Physics.DevMohapatraHeavyElimination.residual_factor,
  GUT.DevMohapatraHeavyElimination.s => Physics.DevMohapatraHeavyElimination.s,
  GUT.DevMohapatraHeavyElimination.sb => Physics.DevMohapatraHeavyElimination.sb,
  GUT.DevMohapatraHeavyElimination.solution => Physics.DevMohapatraHeavyElimination.solution,
  GUT.DevMohapatraHeavyElimination.solution.eq_1 => Physics.DevMohapatraHeavyElimination.solution.eq_1,
  GUT.DevMohapatraHeavyElimination.solution_odd => Physics.DevMohapatraHeavyElimination.solution_odd,
  GUT.DevMohapatraHeavyElimination.source => Physics.DevMohapatraHeavyElimination.source,
  GUT.DevMohapatraHeavyElimination.source.eq_1 => Physics.DevMohapatraHeavyElimination.source.eq_1,
  GUT.DevMohapatraHeavyElimination.source_equation => Physics.DevMohapatraHeavyElimination.source_equation,
  GUT.DevMohapatraHeavyElimination.source_odd => Physics.DevMohapatraHeavyElimination.source_odd,
  GUT.DevMohapatraHeavyElimination.source_unique => Physics.DevMohapatraHeavyElimination.source_unique,
  GUT.DevMohapatraHeavyElimination.stationary => Physics.DevMohapatraHeavyElimination.stationary,
  GUT.DevMohapatraHeavyElimination.stationary_unique => Physics.DevMohapatraHeavyElimination.stationary_unique,
  GUT.DevMohapatraHeavyElimination.u => Physics.DevMohapatraHeavyElimination.u,
  GUT.DevMohapatraHeavyElimination.ub => Physics.DevMohapatraHeavyElimination.ub
]

assert_compatible GUT.DevMohapatraHeavyElimination.R => Physics.DevMohapatraHeavyElimination.R
assert_compatible GUT.DevMohapatraHeavyElimination.V => Physics.DevMohapatraHeavyElimination.V
assert_compatible GUT.DevMohapatraHeavyElimination.action => Physics.DevMohapatraHeavyElimination.action
assert_compatible GUT.DevMohapatraHeavyElimination.action.eq_1 => Physics.DevMohapatraHeavyElimination.action.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.constant => Physics.DevMohapatraHeavyElimination.constant
assert_compatible GUT.DevMohapatraHeavyElimination.coord => Physics.DevMohapatraHeavyElimination.coord
assert_compatible GUT.DevMohapatraHeavyElimination.cross => Physics.DevMohapatraHeavyElimination.cross
assert_compatible GUT.DevMohapatraHeavyElimination.cross.eq_1 => Physics.DevMohapatraHeavyElimination.cross.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.cross_commutes => Physics.DevMohapatraHeavyElimination.cross_commutes
assert_compatible GUT.DevMohapatraHeavyElimination.cross_degree => Physics.DevMohapatraHeavyElimination.cross_degree
assert_compatible GUT.DevMohapatraHeavyElimination.cross_even => Physics.DevMohapatraHeavyElimination.cross_even
assert_compatible GUT.DevMohapatraHeavyElimination.current_odd => Physics.DevMohapatraHeavyElimination.current_odd
assert_compatible GUT.DevMohapatraHeavyElimination.d => Physics.DevMohapatraHeavyElimination.d
assert_compatible GUT.DevMohapatraHeavyElimination.db => Physics.DevMohapatraHeavyElimination.db
assert_compatible GUT.DevMohapatraHeavyElimination.eliminated_action => Physics.DevMohapatraHeavyElimination.eliminated_action
assert_compatible GUT.DevMohapatraHeavyElimination.euler => Physics.DevMohapatraHeavyElimination.euler
assert_compatible GUT.DevMohapatraHeavyElimination.kernel => Physics.DevMohapatraHeavyElimination.kernel
assert_compatible GUT.DevMohapatraHeavyElimination.kernel.eq_1 => Physics.DevMohapatraHeavyElimination.kernel.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.kernel_degree => Physics.DevMohapatraHeavyElimination.kernel_degree
assert_compatible GUT.DevMohapatraHeavyElimination.kernel_even => Physics.DevMohapatraHeavyElimination.kernel_even
assert_compatible GUT.DevMohapatraHeavyElimination.kernel_nilpotent => Physics.DevMohapatraHeavyElimination.kernel_nilpotent
assert_compatible GUT.DevMohapatraHeavyElimination.kernel_preserves_odd => Physics.DevMohapatraHeavyElimination.kernel_preserves_odd
assert_compatible GUT.DevMohapatraHeavyElimination.linear => Physics.DevMohapatraHeavyElimination.linear
assert_compatible GUT.DevMohapatraHeavyElimination.linear.eq_1 => Physics.DevMohapatraHeavyElimination.linear.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.quadratic => Physics.DevMohapatraHeavyElimination.quadratic
assert_compatible GUT.DevMohapatraHeavyElimination.quadratic.eq_1 => Physics.DevMohapatraHeavyElimination.quadratic.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.residual => Physics.DevMohapatraHeavyElimination.residual
assert_compatible GUT.DevMohapatraHeavyElimination.residual.eq_1 => Physics.DevMohapatraHeavyElimination.residual.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.residual_factor => Physics.DevMohapatraHeavyElimination.residual_factor
assert_compatible GUT.DevMohapatraHeavyElimination.s => Physics.DevMohapatraHeavyElimination.s
assert_compatible GUT.DevMohapatraHeavyElimination.sb => Physics.DevMohapatraHeavyElimination.sb
assert_compatible GUT.DevMohapatraHeavyElimination.solution => Physics.DevMohapatraHeavyElimination.solution
assert_compatible GUT.DevMohapatraHeavyElimination.solution.eq_1 => Physics.DevMohapatraHeavyElimination.solution.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.solution_odd => Physics.DevMohapatraHeavyElimination.solution_odd
assert_compatible GUT.DevMohapatraHeavyElimination.source => Physics.DevMohapatraHeavyElimination.source
assert_compatible GUT.DevMohapatraHeavyElimination.source.eq_1 => Physics.DevMohapatraHeavyElimination.source.eq_1
assert_compatible GUT.DevMohapatraHeavyElimination.source_equation => Physics.DevMohapatraHeavyElimination.source_equation
assert_compatible GUT.DevMohapatraHeavyElimination.source_odd => Physics.DevMohapatraHeavyElimination.source_odd
assert_compatible GUT.DevMohapatraHeavyElimination.source_unique => Physics.DevMohapatraHeavyElimination.source_unique
assert_compatible GUT.DevMohapatraHeavyElimination.stationary => Physics.DevMohapatraHeavyElimination.stationary
assert_compatible GUT.DevMohapatraHeavyElimination.stationary_unique => Physics.DevMohapatraHeavyElimination.stationary_unique
assert_compatible GUT.DevMohapatraHeavyElimination.u => Physics.DevMohapatraHeavyElimination.u
assert_compatible GUT.DevMohapatraHeavyElimination.ub => Physics.DevMohapatraHeavyElimination.ub
