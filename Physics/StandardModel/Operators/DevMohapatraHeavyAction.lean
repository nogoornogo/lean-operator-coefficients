import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyAction
import Physics.StandardModel.Operators.DevMohapatraHeavyElimination
import Math.LinearAlgebra.ExteriorLeftDerivative
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraHeavyAction.B => Physics.DevMohapatraHeavyAction.B,
  GUT.DevMohapatraHeavyAction.W => Physics.DevMohapatraHeavyAction.W,
  GUT.DevMohapatraHeavyAction.derivative => Physics.DevMohapatraHeavyAction.derivative,
  GUT.DevMohapatraHeavyAction.derivative.eq_1 => Physics.DevMohapatraHeavyAction.derivative.eq_1,
  GUT.DevMohapatraHeavyAction.derivative_external => Physics.DevMohapatraHeavyAction.derivative_external,
  GUT.DevMohapatraHeavyAction.derivative_heavy => Physics.DevMohapatraHeavyAction.derivative_heavy,
  GUT.DevMohapatraHeavyAction.derivative_mul => Physics.DevMohapatraHeavyAction.derivative_mul,
  GUT.DevMohapatraHeavyAction.differentiated_action => Physics.DevMohapatraHeavyAction.differentiated_action,
  GUT.DevMohapatraHeavyAction.dual => Physics.DevMohapatraHeavyAction.dual,
  GUT.DevMohapatraHeavyAction.dual.eq_1 => Physics.DevMohapatraHeavyAction.dual.eq_1,
  GUT.DevMohapatraHeavyAction.eliminated_action => Physics.DevMohapatraHeavyAction.eliminated_action,
  GUT.DevMohapatraHeavyAction.evalLinear => Physics.DevMohapatraHeavyAction.evalLinear,
  GUT.DevMohapatraHeavyAction.evalLinear.eq_1 => Physics.DevMohapatraHeavyAction.evalLinear.eq_1,
  GUT.DevMohapatraHeavyAction.evalLinear_odd => Physics.DevMohapatraHeavyAction.evalLinear_odd,
  GUT.DevMohapatraHeavyAction.evaluate => Physics.DevMohapatraHeavyAction.evaluate,
  GUT.DevMohapatraHeavyAction.evaluate.congr_simp => Physics.DevMohapatraHeavyAction.evaluate.congr_simp,
  GUT.DevMohapatraHeavyAction.evaluate.eq_1 => Physics.DevMohapatraHeavyAction.evaluate.eq_1,
  GUT.DevMohapatraHeavyAction.evaluate_external => Physics.DevMohapatraHeavyAction.evaluate_external,
  GUT.DevMohapatraHeavyAction.evaluate_heavy => Physics.DevMohapatraHeavyAction.evaluate_heavy,
  GUT.DevMohapatraHeavyAction.evaluated_action => Physics.DevMohapatraHeavyAction.evaluated_action,
  GUT.DevMohapatraHeavyAction.heavy => Physics.DevMohapatraHeavyAction.heavy,
  GUT.DevMohapatraHeavyAction.heavy.eq_1 => Physics.DevMohapatraHeavyAction.heavy.eq_1,
  GUT.DevMohapatraHeavyAction.heavyVector => Physics.DevMohapatraHeavyAction.heavyVector,
  GUT.DevMohapatraHeavyAction.heavyVector.eq_1 => Physics.DevMohapatraHeavyAction.heavyVector.eq_1,
  GUT.DevMohapatraHeavyAction.heavy_odd => Physics.DevMohapatraHeavyAction.heavy_odd,
  GUT.DevMohapatraHeavyAction.includeExternal => Physics.DevMohapatraHeavyAction.includeExternal,
  GUT.DevMohapatraHeavyAction.includeExternal.eq_1 => Physics.DevMohapatraHeavyAction.includeExternal.eq_1,
  GUT.DevMohapatraHeavyAction.stationary => Physics.DevMohapatraHeavyAction.stationary,
  GUT.DevMohapatraHeavyAction.stationary_unique => Physics.DevMohapatraHeavyAction.stationary_unique,
  GUT.DevMohapatraHeavyAction.universalAction => Physics.DevMohapatraHeavyAction.universalAction,
  GUT.DevMohapatraHeavyAction.universalAction.eq_1 => Physics.DevMohapatraHeavyAction.universalAction.eq_1
]

assert_compatible GUT.DevMohapatraHeavyAction.B => Physics.DevMohapatraHeavyAction.B
assert_compatible GUT.DevMohapatraHeavyAction.W => Physics.DevMohapatraHeavyAction.W
assert_compatible GUT.DevMohapatraHeavyAction.derivative => Physics.DevMohapatraHeavyAction.derivative
assert_compatible GUT.DevMohapatraHeavyAction.derivative.eq_1 => Physics.DevMohapatraHeavyAction.derivative.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.derivative_external => Physics.DevMohapatraHeavyAction.derivative_external
assert_compatible GUT.DevMohapatraHeavyAction.derivative_heavy => Physics.DevMohapatraHeavyAction.derivative_heavy
assert_compatible GUT.DevMohapatraHeavyAction.derivative_mul => Physics.DevMohapatraHeavyAction.derivative_mul
assert_compatible GUT.DevMohapatraHeavyAction.differentiated_action => Physics.DevMohapatraHeavyAction.differentiated_action
assert_compatible GUT.DevMohapatraHeavyAction.dual => Physics.DevMohapatraHeavyAction.dual
assert_compatible GUT.DevMohapatraHeavyAction.dual.eq_1 => Physics.DevMohapatraHeavyAction.dual.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.eliminated_action => Physics.DevMohapatraHeavyAction.eliminated_action
assert_compatible GUT.DevMohapatraHeavyAction.evalLinear => Physics.DevMohapatraHeavyAction.evalLinear
assert_compatible GUT.DevMohapatraHeavyAction.evalLinear.eq_1 => Physics.DevMohapatraHeavyAction.evalLinear.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.evalLinear_odd => Physics.DevMohapatraHeavyAction.evalLinear_odd
assert_compatible GUT.DevMohapatraHeavyAction.evaluate => Physics.DevMohapatraHeavyAction.evaluate
assert_compatible GUT.DevMohapatraHeavyAction.evaluate.congr_simp => Physics.DevMohapatraHeavyAction.evaluate.congr_simp
assert_compatible GUT.DevMohapatraHeavyAction.evaluate.eq_1 => Physics.DevMohapatraHeavyAction.evaluate.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.evaluate_external => Physics.DevMohapatraHeavyAction.evaluate_external
assert_compatible GUT.DevMohapatraHeavyAction.evaluate_heavy => Physics.DevMohapatraHeavyAction.evaluate_heavy
assert_compatible GUT.DevMohapatraHeavyAction.evaluated_action => Physics.DevMohapatraHeavyAction.evaluated_action
assert_compatible GUT.DevMohapatraHeavyAction.heavy => Physics.DevMohapatraHeavyAction.heavy
assert_compatible GUT.DevMohapatraHeavyAction.heavy.eq_1 => Physics.DevMohapatraHeavyAction.heavy.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.heavyVector => Physics.DevMohapatraHeavyAction.heavyVector
assert_compatible GUT.DevMohapatraHeavyAction.heavyVector.eq_1 => Physics.DevMohapatraHeavyAction.heavyVector.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.heavy_odd => Physics.DevMohapatraHeavyAction.heavy_odd
assert_compatible GUT.DevMohapatraHeavyAction.includeExternal => Physics.DevMohapatraHeavyAction.includeExternal
assert_compatible GUT.DevMohapatraHeavyAction.includeExternal.eq_1 => Physics.DevMohapatraHeavyAction.includeExternal.eq_1
assert_compatible GUT.DevMohapatraHeavyAction.stationary => Physics.DevMohapatraHeavyAction.stationary
assert_compatible GUT.DevMohapatraHeavyAction.stationary_unique => Physics.DevMohapatraHeavyAction.stationary_unique
assert_compatible GUT.DevMohapatraHeavyAction.universalAction => Physics.DevMohapatraHeavyAction.universalAction
assert_compatible GUT.DevMohapatraHeavyAction.universalAction.eq_1 => Physics.DevMohapatraHeavyAction.universalAction.eq_1
