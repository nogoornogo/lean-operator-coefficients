import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInternal
import Physics.FieldTheory.Jets.WeylHiggsWaveInternalFields
import Physics.FieldTheory.Jets.WeylHiggsWaveLorentz
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInternal instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveInternal.derivative_internal => Physics.WeylHiggsWaveInternal.derivative_internal,
  GUT.WeylHiggsWaveInternal.derivative_psi_internal => Physics.WeylHiggsWaveInternal.derivative_psi_internal,
  GUT.WeylHiggsWaveInternal.even_word_invariant => Physics.WeylHiggsWaveInternal.even_word_invariant,
  GUT.WeylHiggsWaveInternal.first_word_invariant => Physics.WeylHiggsWaveInternal.first_word_invariant,
  GUT.WeylHiggsWaveInternal.instAddCommGroupA_physics => Physics.WeylHiggsWaveInternal.instAddCommGroupA_physics,
  GUT.WeylHiggsWaveInternal.instModuleComplexA_physics => Physics.WeylHiggsWaveInternal.instModuleComplexA_physics,
  GUT.WeylHiggsWaveInternal.instRingA_physics => Physics.WeylHiggsWaveInternal.instRingA_physics,
  GUT.WeylHiggsWaveInternal.invariant => Physics.WeylHiggsWaveInternal.invariant,
  GUT.WeylHiggsWaveInternal.positive_odd_zero => Physics.WeylHiggsWaveInternal.positive_odd_zero,
  GUT.WeylHiggsWaveInternal.primitive_covariant => Physics.WeylHiggsWaveInternal.primitive_covariant,
  GUT.WeylHiggsWaveInternal.primitive_invariant => Physics.WeylHiggsWaveInternal.primitive_invariant,
  GUT.WeylHiggsWaveInternal.psi_internal => Physics.WeylHiggsWaveInternal.psi_internal,
  GUT.WeylHiggsWaveInternal.second_word_invariant => Physics.WeylHiggsWaveInternal.second_word_invariant,
  GUT.WeylHiggsWaveInternal.word_invariant => Physics.WeylHiggsWaveInternal.word_invariant
]

assert_compatible GUT.WeylHiggsWaveInternal.derivative_internal => Physics.WeylHiggsWaveInternal.derivative_internal
assert_compatible GUT.WeylHiggsWaveInternal.derivative_psi_internal => Physics.WeylHiggsWaveInternal.derivative_psi_internal
assert_compatible GUT.WeylHiggsWaveInternal.even_word_invariant => Physics.WeylHiggsWaveInternal.even_word_invariant
assert_compatible GUT.WeylHiggsWaveInternal.first_word_invariant => Physics.WeylHiggsWaveInternal.first_word_invariant
assert_compatible GUT.WeylHiggsWaveInternal.instAddCommGroupA_physics => Physics.WeylHiggsWaveInternal.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsWaveInternal.instModuleComplexA_physics => Physics.WeylHiggsWaveInternal.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsWaveInternal.instRingA_physics => Physics.WeylHiggsWaveInternal.instRingA_physics
assert_compatible GUT.WeylHiggsWaveInternal.invariant => Physics.WeylHiggsWaveInternal.invariant
assert_compatible GUT.WeylHiggsWaveInternal.positive_odd_zero => Physics.WeylHiggsWaveInternal.positive_odd_zero
assert_compatible GUT.WeylHiggsWaveInternal.primitive_covariant => Physics.WeylHiggsWaveInternal.primitive_covariant
assert_compatible GUT.WeylHiggsWaveInternal.primitive_invariant => Physics.WeylHiggsWaveInternal.primitive_invariant
assert_compatible GUT.WeylHiggsWaveInternal.psi_internal => Physics.WeylHiggsWaveInternal.psi_internal
assert_compatible GUT.WeylHiggsWaveInternal.second_word_invariant => Physics.WeylHiggsWaveInternal.second_word_invariant
assert_compatible GUT.WeylHiggsWaveInternal.word_invariant => Physics.WeylHiggsWaveInternal.word_invariant
