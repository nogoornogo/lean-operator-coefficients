import Physics.FieldTheory.Jets.Weyl.Equations.WeylLinearEquation
import Math.Algebra.LinearJetEquation
import Physics.FieldTheory.Jets.LorentzJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylLinearEquation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylLinearEquation.Coordinates => Physics.WeylLinearEquation.Coordinates,
  GUT.WeylLinearEquation.Equations => Physics.WeylLinearEquation.Equations,
  GUT.WeylLinearEquation.Generator => Physics.WeylLinearEquation.Generator,
  GUT.WeylLinearEquation.Group => Physics.WeylLinearEquation.Group,
  GUT.WeylLinearEquation.Jets => Physics.WeylLinearEquation.Jets,
  GUT.WeylLinearEquation.Spinor => Physics.WeylLinearEquation.Spinor,
  GUT.WeylLinearEquation.action => Physics.WeylLinearEquation.action,
  GUT.WeylLinearEquation.contract => Physics.WeylLinearEquation.contract,
  GUT.WeylLinearEquation.contractMatrix => Physics.WeylLinearEquation.contractMatrix,
  GUT.WeylLinearEquation.contract_covariant => Physics.WeylLinearEquation.contract_covariant,
  GUT.WeylLinearEquation.contract_matrix => Physics.WeylLinearEquation.contract_matrix,
  GUT.WeylLinearEquation.descendant_zero => Physics.WeylLinearEquation.descendant_zero,
  GUT.WeylLinearEquation.expand => Physics.WeylLinearEquation.expand,
  GUT.WeylLinearEquation.frame => Physics.WeylLinearEquation.frame,
  GUT.WeylLinearEquation.frame.eq_1 => Physics.WeylLinearEquation.frame.eq_1,
  GUT.WeylLinearEquation.frame_covariant => Physics.WeylLinearEquation.frame_covariant,
  GUT.WeylLinearEquation.relations => Physics.WeylLinearEquation.relations,
  GUT.WeylLinearEquation.seed => Physics.WeylLinearEquation.seed,
  GUT.WeylLinearEquation.seed_covariant => Physics.WeylLinearEquation.seed_covariant
]

assert_compatible GUT.WeylLinearEquation.Coordinates => Physics.WeylLinearEquation.Coordinates
assert_compatible GUT.WeylLinearEquation.Equations => Physics.WeylLinearEquation.Equations
assert_compatible GUT.WeylLinearEquation.Generator => Physics.WeylLinearEquation.Generator
assert_compatible GUT.WeylLinearEquation.Group => Physics.WeylLinearEquation.Group
assert_compatible GUT.WeylLinearEquation.Jets => Physics.WeylLinearEquation.Jets
assert_compatible GUT.WeylLinearEquation.Spinor => Physics.WeylLinearEquation.Spinor
assert_compatible GUT.WeylLinearEquation.action => Physics.WeylLinearEquation.action
assert_compatible GUT.WeylLinearEquation.contract => Physics.WeylLinearEquation.contract
assert_compatible GUT.WeylLinearEquation.contractMatrix => Physics.WeylLinearEquation.contractMatrix
assert_compatible GUT.WeylLinearEquation.contract_covariant => Physics.WeylLinearEquation.contract_covariant
assert_compatible GUT.WeylLinearEquation.contract_matrix => Physics.WeylLinearEquation.contract_matrix
assert_compatible GUT.WeylLinearEquation.descendant_zero => Physics.WeylLinearEquation.descendant_zero
assert_compatible GUT.WeylLinearEquation.expand => Physics.WeylLinearEquation.expand
assert_compatible GUT.WeylLinearEquation.frame => Physics.WeylLinearEquation.frame
assert_compatible GUT.WeylLinearEquation.frame.eq_1 => Physics.WeylLinearEquation.frame.eq_1
assert_compatible GUT.WeylLinearEquation.frame_covariant => Physics.WeylLinearEquation.frame_covariant
assert_compatible GUT.WeylLinearEquation.relations => Physics.WeylLinearEquation.relations
assert_compatible GUT.WeylLinearEquation.seed => Physics.WeylLinearEquation.seed
assert_compatible GUT.WeylLinearEquation.seed_covariant => Physics.WeylLinearEquation.seed_covariant
