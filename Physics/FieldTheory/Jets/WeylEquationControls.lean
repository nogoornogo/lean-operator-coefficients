import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationControls
import Physics.FieldTheory.Jets.WeylLinearEquation
import Math.Algebra.LinearJetAlgebra
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzJetIBP.spinorBasis.eq_1 => Physics.LorentzJetIBP.spinorBasis.eq_1,
  GUT.WeylLinearEquation.field_expansion => Physics.WeylLinearEquation.field_expansion,
  GUT.WeylLinearEquation.higher_jet_survives => Physics.WeylLinearEquation.higher_jet_survives,
  GUT.WeylLinearEquation.nullPoint => Physics.WeylLinearEquation.nullPoint,
  GUT.WeylLinearEquation.nullPoint.eq_1 => Physics.WeylLinearEquation.nullPoint.eq_1,
  GUT.WeylLinearEquation.odd_higher_jet_survives => Physics.WeylLinearEquation.odd_higher_jet_survives,
  GUT.WeylLinearEquation.onShellProbe => Physics.WeylLinearEquation.onShellProbe,
  GUT.WeylLinearEquation.probe => Physics.WeylLinearEquation.probe,
  GUT.WeylLinearEquation.probe.eq_1 => Physics.WeylLinearEquation.probe.eq_1,
  GUT.WeylLinearEquation.probe_annihilates => Physics.WeylLinearEquation.probe_annihilates,
  GUT.WeylLinearEquation.probe_multiple => Physics.WeylLinearEquation.probe_multiple,
  GUT.WeylLinearEquation.probe_ofSymbols => Physics.WeylLinearEquation.probe_ofSymbols,
  GUT.WeylLinearEquation.probe_seed => Physics.WeylLinearEquation.probe_seed,
  GUT.WeylLinearEquation.probe_shift => Physics.WeylLinearEquation.probe_shift,
  GUT.WeylLinearEquation.row => Physics.WeylLinearEquation.row,
  GUT.WeylLinearEquation.seed_row_ne_zero => Physics.WeylLinearEquation.seed_row_ne_zero,
  GUT.WeylLinearEquation.seed_row_one => Physics.WeylLinearEquation.seed_row_one,
  GUT.WeylLinearEquation.seed_row_zero => Physics.WeylLinearEquation.seed_row_zero,
  GUT.WeylLinearEquation.shift_field => Physics.WeylLinearEquation.shift_field,
  GUT.WeylLinearEquation.wave_descendants => Physics.WeylLinearEquation.wave_descendants,
  GUT.WeylLinearEquation.wave_one_relation => Physics.WeylLinearEquation.wave_one_relation,
  GUT.WeylLinearEquation.wave_zero_relation => Physics.WeylLinearEquation.wave_zero_relation
]

assert_compatible GUT.LorentzJetIBP.spinorBasis.eq_1 => Physics.LorentzJetIBP.spinorBasis.eq_1
assert_compatible GUT.WeylLinearEquation.field_expansion => Physics.WeylLinearEquation.field_expansion
assert_compatible GUT.WeylLinearEquation.higher_jet_survives => Physics.WeylLinearEquation.higher_jet_survives
assert_compatible GUT.WeylLinearEquation.nullPoint => Physics.WeylLinearEquation.nullPoint
assert_compatible GUT.WeylLinearEquation.nullPoint.eq_1 => Physics.WeylLinearEquation.nullPoint.eq_1
assert_compatible GUT.WeylLinearEquation.odd_higher_jet_survives => Physics.WeylLinearEquation.odd_higher_jet_survives
assert_compatible GUT.WeylLinearEquation.onShellProbe => Physics.WeylLinearEquation.onShellProbe
assert_compatible GUT.WeylLinearEquation.probe => Physics.WeylLinearEquation.probe
assert_compatible GUT.WeylLinearEquation.probe.eq_1 => Physics.WeylLinearEquation.probe.eq_1
assert_compatible GUT.WeylLinearEquation.probe_annihilates => Physics.WeylLinearEquation.probe_annihilates
assert_compatible GUT.WeylLinearEquation.probe_multiple => Physics.WeylLinearEquation.probe_multiple
assert_compatible GUT.WeylLinearEquation.probe_ofSymbols => Physics.WeylLinearEquation.probe_ofSymbols
assert_compatible GUT.WeylLinearEquation.probe_seed => Physics.WeylLinearEquation.probe_seed
assert_compatible GUT.WeylLinearEquation.probe_shift => Physics.WeylLinearEquation.probe_shift
assert_compatible GUT.WeylLinearEquation.row => Physics.WeylLinearEquation.row
assert_compatible GUT.WeylLinearEquation.seed_row_ne_zero => Physics.WeylLinearEquation.seed_row_ne_zero
assert_compatible GUT.WeylLinearEquation.seed_row_one => Physics.WeylLinearEquation.seed_row_one
assert_compatible GUT.WeylLinearEquation.seed_row_zero => Physics.WeylLinearEquation.seed_row_zero
assert_compatible GUT.WeylLinearEquation.shift_field => Physics.WeylLinearEquation.shift_field
assert_compatible GUT.WeylLinearEquation.wave_descendants => Physics.WeylLinearEquation.wave_descendants
assert_compatible GUT.WeylLinearEquation.wave_one_relation => Physics.WeylLinearEquation.wave_one_relation
assert_compatible GUT.WeylLinearEquation.wave_zero_relation => Physics.WeylLinearEquation.wave_zero_relation
