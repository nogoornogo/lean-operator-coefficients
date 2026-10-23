import Physics.FieldTheory.Jets.Gauge.MaxwellLinearEquation
import Physics.FieldTheory.Jets.AbelianFieldStrength
import Math.Algebra.LinearJetEquation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.MaxwellLinearEquation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AbelianFieldStrength.Equations => Physics.AbelianFieldStrength.Equations,
  GUT.AbelianFieldStrength.Generator => Physics.AbelianFieldStrength.Generator,
  GUT.AbelianFieldStrength.action => Physics.AbelianFieldStrength.action,
  GUT.AbelianFieldStrength.antisymmetry => Physics.AbelianFieldStrength.antisymmetry,
  GUT.AbelianFieldStrength.antisymmetry.eq_1 => Physics.AbelianFieldStrength.antisymmetry.eq_1,
  GUT.AbelianFieldStrength.antisymmetry_covariant => Physics.AbelianFieldStrength.antisymmetry_covariant,
  GUT.AbelianFieldStrength.antisymmetry_mem => Physics.AbelianFieldStrength.antisymmetry_mem,
  GUT.AbelianFieldStrength.antisymmetry_tmul => Physics.AbelianFieldStrength.antisymmetry_tmul,
  GUT.AbelianFieldStrength.bianchi => Physics.AbelianFieldStrength.bianchi,
  GUT.AbelianFieldStrength.bianchi.eq_1 => Physics.AbelianFieldStrength.bianchi.eq_1,
  GUT.AbelianFieldStrength.bianchi_covariant => Physics.AbelianFieldStrength.bianchi_covariant,
  GUT.AbelianFieldStrength.bianchi_mem => Physics.AbelianFieldStrength.bianchi_mem,
  GUT.AbelianFieldStrength.bianchi_tmul => Physics.AbelianFieldStrength.bianchi_tmul,
  GUT.AbelianFieldStrength.cycle => Physics.AbelianFieldStrength.cycle,
  GUT.AbelianFieldStrength.cycle.eq_1 => Physics.AbelianFieldStrength.cycle.eq_1,
  GUT.AbelianFieldStrength.cycle_tmul => Physics.AbelianFieldStrength.cycle_tmul,
  GUT.AbelianFieldStrength.descendant_zero => Physics.AbelianFieldStrength.descendant_zero,
  GUT.AbelianFieldStrength.equationAction => Physics.AbelianFieldStrength.equationAction,
  GUT.AbelianFieldStrength.first => Physics.AbelianFieldStrength.first,
  GUT.AbelianFieldStrength.first_tmul => Physics.AbelianFieldStrength.first_tmul,
  GUT.AbelianFieldStrength.maxwell => Physics.AbelianFieldStrength.maxwell,
  GUT.AbelianFieldStrength.maxwell.eq_1 => Physics.AbelianFieldStrength.maxwell.eq_1,
  GUT.AbelianFieldStrength.maxwell_apply => Physics.AbelianFieldStrength.maxwell_apply,
  GUT.AbelianFieldStrength.maxwell_covariant => Physics.AbelianFieldStrength.maxwell_covariant,
  GUT.AbelianFieldStrength.maxwell_mem => Physics.AbelianFieldStrength.maxwell_mem,
  GUT.AbelianFieldStrength.relations => Physics.AbelianFieldStrength.relations,
  GUT.AbelianFieldStrength.seed => Physics.AbelianFieldStrength.seed,
  GUT.AbelianFieldStrength.seed.eq_1 => Physics.AbelianFieldStrength.seed.eq_1,
  GUT.AbelianFieldStrength.seed_covariant => Physics.AbelianFieldStrength.seed_covariant
]

assert_compatible GUT.AbelianFieldStrength.Equations => Physics.AbelianFieldStrength.Equations
assert_compatible GUT.AbelianFieldStrength.Generator => Physics.AbelianFieldStrength.Generator
assert_compatible GUT.AbelianFieldStrength.action => Physics.AbelianFieldStrength.action
assert_compatible GUT.AbelianFieldStrength.antisymmetry => Physics.AbelianFieldStrength.antisymmetry
assert_compatible GUT.AbelianFieldStrength.antisymmetry.eq_1 => Physics.AbelianFieldStrength.antisymmetry.eq_1
assert_compatible GUT.AbelianFieldStrength.antisymmetry_covariant => Physics.AbelianFieldStrength.antisymmetry_covariant
assert_compatible GUT.AbelianFieldStrength.antisymmetry_mem => Physics.AbelianFieldStrength.antisymmetry_mem
assert_compatible GUT.AbelianFieldStrength.antisymmetry_tmul => Physics.AbelianFieldStrength.antisymmetry_tmul
assert_compatible GUT.AbelianFieldStrength.bianchi => Physics.AbelianFieldStrength.bianchi
assert_compatible GUT.AbelianFieldStrength.bianchi.eq_1 => Physics.AbelianFieldStrength.bianchi.eq_1
assert_compatible GUT.AbelianFieldStrength.bianchi_covariant => Physics.AbelianFieldStrength.bianchi_covariant
assert_compatible GUT.AbelianFieldStrength.bianchi_mem => Physics.AbelianFieldStrength.bianchi_mem
assert_compatible GUT.AbelianFieldStrength.bianchi_tmul => Physics.AbelianFieldStrength.bianchi_tmul
assert_compatible GUT.AbelianFieldStrength.cycle => Physics.AbelianFieldStrength.cycle
assert_compatible GUT.AbelianFieldStrength.cycle.eq_1 => Physics.AbelianFieldStrength.cycle.eq_1
assert_compatible GUT.AbelianFieldStrength.cycle_tmul => Physics.AbelianFieldStrength.cycle_tmul
assert_compatible GUT.AbelianFieldStrength.descendant_zero => Physics.AbelianFieldStrength.descendant_zero
assert_compatible GUT.AbelianFieldStrength.equationAction => Physics.AbelianFieldStrength.equationAction
assert_compatible GUT.AbelianFieldStrength.first => Physics.AbelianFieldStrength.first
assert_compatible GUT.AbelianFieldStrength.first_tmul => Physics.AbelianFieldStrength.first_tmul
assert_compatible GUT.AbelianFieldStrength.maxwell => Physics.AbelianFieldStrength.maxwell
assert_compatible GUT.AbelianFieldStrength.maxwell.eq_1 => Physics.AbelianFieldStrength.maxwell.eq_1
assert_compatible GUT.AbelianFieldStrength.maxwell_apply => Physics.AbelianFieldStrength.maxwell_apply
assert_compatible GUT.AbelianFieldStrength.maxwell_covariant => Physics.AbelianFieldStrength.maxwell_covariant
assert_compatible GUT.AbelianFieldStrength.maxwell_mem => Physics.AbelianFieldStrength.maxwell_mem
assert_compatible GUT.AbelianFieldStrength.relations => Physics.AbelianFieldStrength.relations
assert_compatible GUT.AbelianFieldStrength.seed => Physics.AbelianFieldStrength.seed
assert_compatible GUT.AbelianFieldStrength.seed.eq_1 => Physics.AbelianFieldStrength.seed.eq_1
assert_compatible GUT.AbelianFieldStrength.seed_covariant => Physics.AbelianFieldStrength.seed_covariant
