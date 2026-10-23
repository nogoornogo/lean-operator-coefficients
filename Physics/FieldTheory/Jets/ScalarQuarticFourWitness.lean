import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWitness
import Math.Algebra.FourWaveEvaluation
import Physics.FieldTheory.Jets.DerivativeLiteratureScalar
import Physics.FieldTheory.Jets.LorentzFiniteControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWitness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticFourWitness.annihilates => Physics.ScalarQuarticFourWitness.annihilates,
  GUT.ScalarQuarticFourWitness.conservation => Physics.ScalarQuarticFourWitness.conservation,
  GUT.ScalarQuarticFourWitness.ev => Physics.ScalarQuarticFourWitness.ev,
  GUT.ScalarQuarticFourWitness.field_value => Physics.ScalarQuarticFourWitness.field_value,
  GUT.ScalarQuarticFourWitness.first_value => Physics.ScalarQuarticFourWitness.first_value,
  GUT.ScalarQuarticFourWitness.four_value => Physics.ScalarQuarticFourWitness.four_value,
  GUT.ScalarQuarticFourWitness.ideal_zero => Physics.ScalarQuarticFourWitness.ideal_zero,
  GUT.ScalarQuarticFourWitness.kinetic_value => Physics.ScalarQuarticFourWitness.kinetic_value,
  GUT.ScalarQuarticFourWitness.momenta => Physics.ScalarQuarticFourWitness.momenta,
  GUT.ScalarQuarticFourWitness.momenta.eq_1 => Physics.ScalarQuarticFourWitness.momenta.eq_1,
  GUT.ScalarQuarticFourWitness.quotient_nonzero => Physics.ScalarQuarticFourWitness.quotient_nonzero,
  GUT.ScalarQuarticFourWitness.separator => Physics.ScalarQuarticFourWitness.separator,
  GUT.ScalarQuarticFourWitness.separator_after => Physics.ScalarQuarticFourWitness.separator_after,
  GUT.ScalarQuarticFourWitness.separator_before => Physics.ScalarQuarticFourWitness.separator_before,
  GUT.ScalarQuarticFourWitness.separator_not_invariant => Physics.ScalarQuarticFourWitness.separator_not_invariant,
  GUT.ScalarQuarticFourWitness.transformed_first => Physics.ScalarQuarticFourWitness.transformed_first,
  GUT.ScalarQuarticFourWitness.wave_zero => Physics.ScalarQuarticFourWitness.wave_zero
]

assert_compatible GUT.ScalarQuarticFourWitness.annihilates => Physics.ScalarQuarticFourWitness.annihilates
assert_compatible GUT.ScalarQuarticFourWitness.conservation => Physics.ScalarQuarticFourWitness.conservation
assert_compatible GUT.ScalarQuarticFourWitness.ev => Physics.ScalarQuarticFourWitness.ev
assert_compatible GUT.ScalarQuarticFourWitness.field_value => Physics.ScalarQuarticFourWitness.field_value
assert_compatible GUT.ScalarQuarticFourWitness.first_value => Physics.ScalarQuarticFourWitness.first_value
assert_compatible GUT.ScalarQuarticFourWitness.four_value => Physics.ScalarQuarticFourWitness.four_value
assert_compatible GUT.ScalarQuarticFourWitness.ideal_zero => Physics.ScalarQuarticFourWitness.ideal_zero
assert_compatible GUT.ScalarQuarticFourWitness.kinetic_value => Physics.ScalarQuarticFourWitness.kinetic_value
assert_compatible GUT.ScalarQuarticFourWitness.momenta => Physics.ScalarQuarticFourWitness.momenta
assert_compatible GUT.ScalarQuarticFourWitness.momenta.eq_1 => Physics.ScalarQuarticFourWitness.momenta.eq_1
assert_compatible GUT.ScalarQuarticFourWitness.quotient_nonzero => Physics.ScalarQuarticFourWitness.quotient_nonzero
assert_compatible GUT.ScalarQuarticFourWitness.separator => Physics.ScalarQuarticFourWitness.separator
assert_compatible GUT.ScalarQuarticFourWitness.separator_after => Physics.ScalarQuarticFourWitness.separator_after
assert_compatible GUT.ScalarQuarticFourWitness.separator_before => Physics.ScalarQuarticFourWitness.separator_before
assert_compatible GUT.ScalarQuarticFourWitness.separator_not_invariant => Physics.ScalarQuarticFourWitness.separator_not_invariant
assert_compatible GUT.ScalarQuarticFourWitness.transformed_first => Physics.ScalarQuarticFourWitness.transformed_first
assert_compatible GUT.ScalarQuarticFourWitness.wave_zero => Physics.ScalarQuarticFourWitness.wave_zero
