import Physics.FieldTheory.Jets.Gauge.MaxwellWave
import Physics.FieldTheory.Jets.MaxwellLinearEquation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.MaxwellWave instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AbelianFieldStrength.D => Physics.AbelianFieldStrength.D,
  GUT.AbelianFieldStrength.antisymmetry_basis => Physics.AbelianFieldStrength.antisymmetry_basis,
  GUT.AbelianFieldStrength.antisymmetry_descendants => Physics.AbelianFieldStrength.antisymmetry_descendants,
  GUT.AbelianFieldStrength.antisymmetry_zero => Physics.AbelianFieldStrength.antisymmetry_zero,
  GUT.AbelianFieldStrength.bianchi_basis => Physics.AbelianFieldStrength.bianchi_basis,
  GUT.AbelianFieldStrength.bianchi_zero => Physics.AbelianFieldStrength.bianchi_zero,
  GUT.AbelianFieldStrength.component => Physics.AbelianFieldStrength.component,
  GUT.AbelianFieldStrength.component.eq_1 => Physics.AbelianFieldStrength.component.eq_1,
  GUT.AbelianFieldStrength.component_symbol => Physics.AbelianFieldStrength.component_symbol,
  GUT.AbelianFieldStrength.diagonal_descendants => Physics.AbelianFieldStrength.diagonal_descendants,
  GUT.AbelianFieldStrength.fieldClass => Physics.AbelianFieldStrength.fieldClass,
  GUT.AbelianFieldStrength.fieldClass.eq_1 => Physics.AbelianFieldStrength.fieldClass.eq_1,
  GUT.AbelianFieldStrength.maxwell_basis => Physics.AbelianFieldStrength.maxwell_basis,
  GUT.AbelianFieldStrength.maxwell_zero => Physics.AbelianFieldStrength.maxwell_zero,
  GUT.AbelianFieldStrength.wave_descendants => Physics.AbelianFieldStrength.wave_descendants,
  GUT.AbelianFieldStrength.wave_relation => Physics.AbelianFieldStrength.wave_relation,
  GUT.AbelianFieldStrength.wave_zero => Physics.AbelianFieldStrength.wave_zero
]

assert_compatible GUT.AbelianFieldStrength.D => Physics.AbelianFieldStrength.D
assert_compatible GUT.AbelianFieldStrength.antisymmetry_basis => Physics.AbelianFieldStrength.antisymmetry_basis
assert_compatible GUT.AbelianFieldStrength.antisymmetry_descendants => Physics.AbelianFieldStrength.antisymmetry_descendants
assert_compatible GUT.AbelianFieldStrength.antisymmetry_zero => Physics.AbelianFieldStrength.antisymmetry_zero
assert_compatible GUT.AbelianFieldStrength.bianchi_basis => Physics.AbelianFieldStrength.bianchi_basis
assert_compatible GUT.AbelianFieldStrength.bianchi_zero => Physics.AbelianFieldStrength.bianchi_zero
assert_compatible GUT.AbelianFieldStrength.component => Physics.AbelianFieldStrength.component
assert_compatible GUT.AbelianFieldStrength.component.eq_1 => Physics.AbelianFieldStrength.component.eq_1
assert_compatible GUT.AbelianFieldStrength.component_symbol => Physics.AbelianFieldStrength.component_symbol
assert_compatible GUT.AbelianFieldStrength.diagonal_descendants => Physics.AbelianFieldStrength.diagonal_descendants
assert_compatible GUT.AbelianFieldStrength.fieldClass => Physics.AbelianFieldStrength.fieldClass
assert_compatible GUT.AbelianFieldStrength.fieldClass.eq_1 => Physics.AbelianFieldStrength.fieldClass.eq_1
assert_compatible GUT.AbelianFieldStrength.maxwell_basis => Physics.AbelianFieldStrength.maxwell_basis
assert_compatible GUT.AbelianFieldStrength.maxwell_zero => Physics.AbelianFieldStrength.maxwell_zero
assert_compatible GUT.AbelianFieldStrength.wave_descendants => Physics.AbelianFieldStrength.wave_descendants
assert_compatible GUT.AbelianFieldStrength.wave_relation => Physics.AbelianFieldStrength.wave_relation
assert_compatible GUT.AbelianFieldStrength.wave_zero => Physics.AbelianFieldStrength.wave_zero
