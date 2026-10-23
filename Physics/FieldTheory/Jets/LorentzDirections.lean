import Physics.FieldTheory.Jets.Lorentz.LorentzDirections
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.Algebra.JetDirections
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lorentz.LorentzDirections instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzDirections.Coordinates => Physics.LorentzDirections.Coordinates,
  GUT.LorentzDirections.Group => Physics.LorentzDirections.Group,
  GUT.LorentzDirections.Mat => Physics.LorentzDirections.Mat,
  GUT.LorentzDirections.basisEquiv => Physics.LorentzDirections.basisEquiv,
  GUT.LorentzDirections.det_pauli => Physics.LorentzDirections.det_pauli,
  GUT.LorentzDirections.direction => Physics.LorentzDirections.direction,
  GUT.LorentzDirections.direction_single => Physics.LorentzDirections.direction_single,
  GUT.LorentzDirections.dualEquiv => Physics.LorentzDirections.dualEquiv,
  GUT.LorentzDirections.dualEquiv.eq_1 => Physics.LorentzDirections.dualEquiv.eq_1,
  GUT.LorentzDirections.eval_linearForm => Physics.LorentzDirections.eval_linearForm,
  GUT.LorentzDirections.eval_symbolMap_X => Physics.LorentzDirections.eval_symbolMap_X,
  GUT.LorentzDirections.fromPauli => Physics.LorentzDirections.fromPauli,
  GUT.LorentzDirections.fromPauli.eq_1 => Physics.LorentzDirections.fromPauli.eq_1,
  GUT.LorentzDirections.left_right_matrix => Physics.LorentzDirections.left_right_matrix,
  GUT.LorentzDirections.matrixAction => Physics.LorentzDirections.matrixAction,
  GUT.LorentzDirections.matrixAction_apply => Physics.LorentzDirections.matrixAction_apply,
  GUT.LorentzDirections.outer => Physics.LorentzDirections.outer,
  GUT.LorentzDirections.outer.eq_1 => Physics.LorentzDirections.outer.eq_1,
  GUT.LorentzDirections.pauli => Physics.LorentzDirections.pauli,
  GUT.LorentzDirections.pauli.eq_1 => Physics.LorentzDirections.pauli.eq_1,
  GUT.LorentzDirections.pauliEquiv => Physics.LorentzDirections.pauliEquiv,
  GUT.LorentzDirections.pauli_conjugate => Physics.LorentzDirections.pauli_conjugate,
  GUT.LorentzDirections.pauli_real_hermitian => Physics.LorentzDirections.pauli_real_hermitian,
  GUT.LorentzDirections.pauli_vector => Physics.LorentzDirections.pauli_vector,
  GUT.LorentzDirections.preserves_hermitian => Physics.LorentzDirections.preserves_hermitian,
  GUT.LorentzDirections.quadratic => Physics.LorentzDirections.quadratic,
  GUT.LorentzDirections.quadratic_invariant => Physics.LorentzDirections.quadratic_invariant,
  GUT.LorentzDirections.vector => Physics.LorentzDirections.vector,
  GUT.LorentzDirections.vector_preserves_real => Physics.LorentzDirections.vector_preserves_real,
  GUT.LorentzDirections.wave => Physics.LorentzDirections.wave,
  GUT.LorentzDirections.wave.eq_1 => Physics.LorentzDirections.wave.eq_1,
  GUT.LorentzDirections.wave_invariant => Physics.LorentzDirections.wave_invariant
]

assert_compatible GUT.LorentzDirections.Coordinates => Physics.LorentzDirections.Coordinates
assert_compatible GUT.LorentzDirections.Group => Physics.LorentzDirections.Group
assert_compatible GUT.LorentzDirections.Mat => Physics.LorentzDirections.Mat
assert_compatible GUT.LorentzDirections.basisEquiv => Physics.LorentzDirections.basisEquiv
assert_compatible GUT.LorentzDirections.det_pauli => Physics.LorentzDirections.det_pauli
assert_compatible GUT.LorentzDirections.direction => Physics.LorentzDirections.direction
assert_compatible GUT.LorentzDirections.direction_single => Physics.LorentzDirections.direction_single
assert_compatible GUT.LorentzDirections.dualEquiv => Physics.LorentzDirections.dualEquiv
assert_compatible GUT.LorentzDirections.dualEquiv.eq_1 => Physics.LorentzDirections.dualEquiv.eq_1
assert_compatible GUT.LorentzDirections.eval_linearForm => Physics.LorentzDirections.eval_linearForm
assert_compatible GUT.LorentzDirections.eval_symbolMap_X => Physics.LorentzDirections.eval_symbolMap_X
assert_compatible GUT.LorentzDirections.fromPauli => Physics.LorentzDirections.fromPauli
assert_compatible GUT.LorentzDirections.fromPauli.eq_1 => Physics.LorentzDirections.fromPauli.eq_1
assert_compatible GUT.LorentzDirections.left_right_matrix => Physics.LorentzDirections.left_right_matrix
assert_compatible GUT.LorentzDirections.matrixAction => Physics.LorentzDirections.matrixAction
assert_compatible GUT.LorentzDirections.matrixAction_apply => Physics.LorentzDirections.matrixAction_apply
assert_compatible GUT.LorentzDirections.outer => Physics.LorentzDirections.outer
assert_compatible GUT.LorentzDirections.outer.eq_1 => Physics.LorentzDirections.outer.eq_1
assert_compatible GUT.LorentzDirections.pauli => Physics.LorentzDirections.pauli
assert_compatible GUT.LorentzDirections.pauli.eq_1 => Physics.LorentzDirections.pauli.eq_1
assert_compatible GUT.LorentzDirections.pauliEquiv => Physics.LorentzDirections.pauliEquiv
assert_compatible GUT.LorentzDirections.pauli_conjugate => Physics.LorentzDirections.pauli_conjugate
assert_compatible GUT.LorentzDirections.pauli_real_hermitian => Physics.LorentzDirections.pauli_real_hermitian
assert_compatible GUT.LorentzDirections.pauli_vector => Physics.LorentzDirections.pauli_vector
assert_compatible GUT.LorentzDirections.preserves_hermitian => Physics.LorentzDirections.preserves_hermitian
assert_compatible GUT.LorentzDirections.quadratic => Physics.LorentzDirections.quadratic
assert_compatible GUT.LorentzDirections.quadratic_invariant => Physics.LorentzDirections.quadratic_invariant
assert_compatible GUT.LorentzDirections.vector => Physics.LorentzDirections.vector
assert_compatible GUT.LorentzDirections.vector_preserves_real => Physics.LorentzDirections.vector_preserves_real
assert_compatible GUT.LorentzDirections.wave => Physics.LorentzDirections.wave
assert_compatible GUT.LorentzDirections.wave.eq_1 => Physics.LorentzDirections.wave.eq_1
assert_compatible GUT.LorentzDirections.wave_invariant => Physics.LorentzDirections.wave_invariant
