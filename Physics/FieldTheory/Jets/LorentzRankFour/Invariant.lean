import Physics.FieldTheory.Jets.LorentzRankFour.Core.Invariant
import Physics.FieldTheory.Jets.LorentzRankFour.Contractions
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Invariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzDirections.quadratic.eq_1 => Physics.LorentzDirections.quadratic.eq_1,
  GUT.LorentzRankFour.J => Physics.LorentzRankFour.J,
  GUT.LorentzRankFour.J_square => Physics.LorentzRankFour.J_square,
  GUT.LorentzRankFour.invariant_of_components => Physics.LorentzRankFour.invariant_of_components,
  GUT.LorentzRankFour.matrix => Physics.LorentzRankFour.matrix,
  GUT.LorentzRankFour.matrix_column => Physics.LorentzRankFour.matrix_column,
  GUT.LorentzRankFour.matrix_inverse => Physics.LorentzRankFour.matrix_inverse,
  GUT.LorentzRankFour.matrix_row => Physics.LorentzRankFour.matrix_row,
  GUT.LorentzRankFour.matrix_row_entry => Physics.LorentzRankFour.matrix_row_entry,
  GUT.LorentzRankFour.metricPair => Physics.LorentzRankFour.metricPair,
  GUT.LorentzRankFour.metricPair_apply => Physics.LorentzRankFour.metricPair_apply,
  GUT.LorentzRankFour.metricPair_basis => Physics.LorentzRankFour.metricPair_basis,
  GUT.LorentzRankFour.metricPair_invariant => Physics.LorentzRankFour.metricPair_invariant,
  GUT.LorentzRankFour.metricPair_invariant_basis => Physics.LorentzRankFour.metricPair_invariant_basis,
  GUT.LorentzRankFour.pairing => Physics.LorentzRankFour.pairing,
  GUT.LorentzRankFour.pairing.eq_1 => Physics.LorentzRankFour.pairing.eq_1,
  GUT.LorentzRankFour.pairing_invariant => Physics.LorentzRankFour.pairing_invariant,
  GUT.LorentzRankFour.reconstruct => Physics.LorentzRankFour.reconstruct
]

assert_compatible GUT.LorentzDirections.quadratic.eq_1 => Physics.LorentzDirections.quadratic.eq_1
assert_compatible GUT.LorentzRankFour.J => Physics.LorentzRankFour.J
assert_compatible GUT.LorentzRankFour.J_square => Physics.LorentzRankFour.J_square
assert_compatible GUT.LorentzRankFour.invariant_of_components => Physics.LorentzRankFour.invariant_of_components
assert_compatible GUT.LorentzRankFour.matrix => Physics.LorentzRankFour.matrix
assert_compatible GUT.LorentzRankFour.matrix_column => Physics.LorentzRankFour.matrix_column
assert_compatible GUT.LorentzRankFour.matrix_inverse => Physics.LorentzRankFour.matrix_inverse
assert_compatible GUT.LorentzRankFour.matrix_row => Physics.LorentzRankFour.matrix_row
assert_compatible GUT.LorentzRankFour.matrix_row_entry => Physics.LorentzRankFour.matrix_row_entry
assert_compatible GUT.LorentzRankFour.metricPair => Physics.LorentzRankFour.metricPair
assert_compatible GUT.LorentzRankFour.metricPair_apply => Physics.LorentzRankFour.metricPair_apply
assert_compatible GUT.LorentzRankFour.metricPair_basis => Physics.LorentzRankFour.metricPair_basis
assert_compatible GUT.LorentzRankFour.metricPair_invariant => Physics.LorentzRankFour.metricPair_invariant
assert_compatible GUT.LorentzRankFour.metricPair_invariant_basis => Physics.LorentzRankFour.metricPair_invariant_basis
assert_compatible GUT.LorentzRankFour.pairing => Physics.LorentzRankFour.pairing
assert_compatible GUT.LorentzRankFour.pairing.eq_1 => Physics.LorentzRankFour.pairing.eq_1
assert_compatible GUT.LorentzRankFour.pairing_invariant => Physics.LorentzRankFour.pairing_invariant
assert_compatible GUT.LorentzRankFour.reconstruct => Physics.LorentzRankFour.reconstruct
