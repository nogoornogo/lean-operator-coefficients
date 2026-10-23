import Physics.StandardModel.Gauge.Charges.PhysicalTorus
import Physics.StandardModel.Spectrum.TorusCharacter
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Charges.PhysicalTorus instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SU5.PhysicalTorus.Coordinates => Physics.SU5.PhysicalTorus.Coordinates,
  GUT.SU5.PhysicalTorus.color => Physics.SU5.PhysicalTorus.color,
  GUT.SU5.PhysicalTorus.color.eq_1 => Physics.SU5.PhysicalTorus.color.eq_1,
  GUT.SU5.PhysicalTorus.entries => Physics.SU5.PhysicalTorus.entries,
  GUT.SU5.PhysicalTorus.entries.eq_1 => Physics.SU5.PhysicalTorus.entries.eq_1,
  GUT.SU5.PhysicalTorus.entries_prod => Physics.SU5.PhysicalTorus.entries_prod,
  GUT.SU5.PhysicalTorus.eval_physical_iff => Physics.SU5.PhysicalTorus.eval_physical_iff,
  GUT.SU5.PhysicalTorus.exists_sixth_root => Physics.SU5.PhysicalTorus.exists_sixth_root,
  GUT.SU5.PhysicalTorus.exponent => Physics.SU5.PhysicalTorus.exponent,
  GUT.SU5.PhysicalTorus.exponent.eq_1 => Physics.SU5.PhysicalTorus.exponent.eq_1,
  GUT.SU5.PhysicalTorus.gaugeHom => Physics.SU5.PhysicalTorus.gaugeHom,
  GUT.SU5.PhysicalTorus.gaugePoint => Physics.SU5.PhysicalTorus.gaugePoint,
  GUT.SU5.PhysicalTorus.gaugePoint.eq_1 => Physics.SU5.PhysicalTorus.gaugePoint.eq_1,
  GUT.SU5.PhysicalTorus.toTorus => Physics.SU5.PhysicalTorus.toTorus,
  GUT.SU5.PhysicalTorus.toTorus_surjective => Physics.SU5.PhysicalTorus.toTorus_surjective,
  GUT.SU5.PhysicalTorus.weak => Physics.SU5.PhysicalTorus.weak,
  GUT.SU5.PhysicalTorus.weak.eq_1 => Physics.SU5.PhysicalTorus.weak.eq_1,
  GUT.SU5.PhysicalTorus.weightCharacter_fourier => Physics.SU5.PhysicalTorus.weightCharacter_fourier,
  GUT.SU5.PhysicalTorus.weightCharacter_toTorus => Physics.SU5.PhysicalTorus.weightCharacter_toTorus
]

assert_compatible GUT.SU5.PhysicalTorus.Coordinates => Physics.SU5.PhysicalTorus.Coordinates
assert_compatible GUT.SU5.PhysicalTorus.color => Physics.SU5.PhysicalTorus.color
assert_compatible GUT.SU5.PhysicalTorus.color.eq_1 => Physics.SU5.PhysicalTorus.color.eq_1
assert_compatible GUT.SU5.PhysicalTorus.entries => Physics.SU5.PhysicalTorus.entries
assert_compatible GUT.SU5.PhysicalTorus.entries.eq_1 => Physics.SU5.PhysicalTorus.entries.eq_1
assert_compatible GUT.SU5.PhysicalTorus.entries_prod => Physics.SU5.PhysicalTorus.entries_prod
assert_compatible GUT.SU5.PhysicalTorus.eval_physical_iff => Physics.SU5.PhysicalTorus.eval_physical_iff
assert_compatible GUT.SU5.PhysicalTorus.exists_sixth_root => Physics.SU5.PhysicalTorus.exists_sixth_root
assert_compatible GUT.SU5.PhysicalTorus.exponent => Physics.SU5.PhysicalTorus.exponent
assert_compatible GUT.SU5.PhysicalTorus.exponent.eq_1 => Physics.SU5.PhysicalTorus.exponent.eq_1
assert_compatible GUT.SU5.PhysicalTorus.gaugeHom => Physics.SU5.PhysicalTorus.gaugeHom
assert_compatible GUT.SU5.PhysicalTorus.gaugePoint => Physics.SU5.PhysicalTorus.gaugePoint
assert_compatible GUT.SU5.PhysicalTorus.gaugePoint.eq_1 => Physics.SU5.PhysicalTorus.gaugePoint.eq_1
assert_compatible GUT.SU5.PhysicalTorus.toTorus => Physics.SU5.PhysicalTorus.toTorus
assert_compatible GUT.SU5.PhysicalTorus.toTorus_surjective => Physics.SU5.PhysicalTorus.toTorus_surjective
assert_compatible GUT.SU5.PhysicalTorus.weak => Physics.SU5.PhysicalTorus.weak
assert_compatible GUT.SU5.PhysicalTorus.weak.eq_1 => Physics.SU5.PhysicalTorus.weak.eq_1
assert_compatible GUT.SU5.PhysicalTorus.weightCharacter_fourier => Physics.SU5.PhysicalTorus.weightCharacter_fourier
assert_compatible GUT.SU5.PhysicalTorus.weightCharacter_toTorus => Physics.SU5.PhysicalTorus.weightCharacter_toTorus
