import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveLorentz
import Physics.FieldTheory.Jets.WeylHiggsWaveMoments
import Physics.FieldTheory.Jets.WeylHiggsFirstSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveLorentz instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveLorentz.first_tensor_zero => Physics.WeylHiggsWaveLorentz.first_tensor_zero,
  GUT.WeylHiggsWaveLorentz.invariant => Physics.WeylHiggsWaveLorentz.invariant,
  GUT.WeylHiggsWaveLorentz.invariant_of_zero => Physics.WeylHiggsWaveLorentz.invariant_of_zero,
  GUT.WeylHiggsWaveLorentz.same_tensor_zero => Physics.WeylHiggsWaveLorentz.same_tensor_zero,
  GUT.WeylHiggsWaveLorentz.second_tensor_zero => Physics.WeylHiggsWaveLorentz.second_tensor_zero,
  GUT.WeylHiggsWaveLorentz.tensor_invariant => Physics.WeylHiggsWaveLorentz.tensor_invariant,
  GUT.WeylHiggsWaveLorentz.tensor_zero => Physics.WeylHiggsWaveLorentz.tensor_zero,
  GUT.WeylHiggsWaveLorentz.word_invariant => Physics.WeylHiggsWaveLorentz.word_invariant
]

assert_compatible GUT.WeylHiggsWaveLorentz.first_tensor_zero => Physics.WeylHiggsWaveLorentz.first_tensor_zero
assert_compatible GUT.WeylHiggsWaveLorentz.invariant => Physics.WeylHiggsWaveLorentz.invariant
assert_compatible GUT.WeylHiggsWaveLorentz.invariant_of_zero => Physics.WeylHiggsWaveLorentz.invariant_of_zero
assert_compatible GUT.WeylHiggsWaveLorentz.same_tensor_zero => Physics.WeylHiggsWaveLorentz.same_tensor_zero
assert_compatible GUT.WeylHiggsWaveLorentz.second_tensor_zero => Physics.WeylHiggsWaveLorentz.second_tensor_zero
assert_compatible GUT.WeylHiggsWaveLorentz.tensor_invariant => Physics.WeylHiggsWaveLorentz.tensor_invariant
assert_compatible GUT.WeylHiggsWaveLorentz.tensor_zero => Physics.WeylHiggsWaveLorentz.tensor_zero
assert_compatible GUT.WeylHiggsWaveLorentz.word_invariant => Physics.WeylHiggsWaveLorentz.word_invariant
