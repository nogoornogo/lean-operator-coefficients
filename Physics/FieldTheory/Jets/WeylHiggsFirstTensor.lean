import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstTensor
import Physics.FieldTheory.Jets.WeylHiggsSelection
import Math.Algebra.MixedFirstJetTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsFirstTensor.Dir => Physics.WeylHiggsFirstTensor.Dir,
  GUT.WeylHiggsFirstTensor.Spin => Physics.WeylHiggsFirstTensor.Spin,
  GUT.WeylHiggsFirstTensor.directional_covariant => Physics.WeylHiggsFirstTensor.directional_covariant,
  GUT.WeylHiggsFirstTensor.directional_grade => Physics.WeylHiggsFirstTensor.directional_grade,
  GUT.WeylHiggsFirstTensor.evenField => Physics.WeylHiggsFirstTensor.evenField,
  GUT.WeylHiggsFirstTensor.even_lorentz => Physics.WeylHiggsFirstTensor.even_lorentz,
  GUT.WeylHiggsFirstTensor.instAddCommGroupA_physics => Physics.WeylHiggsFirstTensor.instAddCommGroupA_physics,
  GUT.WeylHiggsFirstTensor.instModuleComplexA_physics => Physics.WeylHiggsFirstTensor.instModuleComplexA_physics,
  GUT.WeylHiggsFirstTensor.instRingA_physics => Physics.WeylHiggsFirstTensor.instRingA_physics,
  GUT.WeylHiggsFirstTensor.oddField => Physics.WeylHiggsFirstTensor.oddField,
  GUT.WeylHiggsFirstTensor.oddField.eq_1 => Physics.WeylHiggsFirstTensor.oddField.eq_1,
  GUT.WeylHiggsFirstTensor.oddField_grade => Physics.WeylHiggsFirstTensor.oddField_grade,
  GUT.WeylHiggsFirstTensor.oddField_single => Physics.WeylHiggsFirstTensor.oddField_single,
  GUT.WeylHiggsFirstTensor.odd_lorentz => Physics.WeylHiggsFirstTensor.odd_lorentz,
  GUT.WeylHiggsFirstTensor.rest => Physics.WeylHiggsFirstTensor.rest,
  GUT.WeylHiggsFirstTensor.rest.eq_1 => Physics.WeylHiggsFirstTensor.rest.eq_1,
  GUT.WeylHiggsFirstTensor.rest_lorentz => Physics.WeylHiggsFirstTensor.rest_lorentz,
  GUT.WeylHiggsFirstTensor.tensor => Physics.WeylHiggsFirstTensor.tensor,
  GUT.WeylHiggsFirstTensor.tensor_apply => Physics.WeylHiggsFirstTensor.tensor_apply,
  GUT.WeylHiggsFirstTensor.tensor_invariant => Physics.WeylHiggsFirstTensor.tensor_invariant,
  GUT.WeylHiggsFirstTensor.transport => Physics.WeylHiggsFirstTensor.transport,
  GUT.WeylHiggsFirstTensor.transport_apply => Physics.WeylHiggsFirstTensor.transport_apply,
  GUT.WeylHiggsFirstTensor.word => Physics.WeylHiggsFirstTensor.word,
  GUT.WeylHiggsFirstTensor.word_grade => Physics.WeylHiggsFirstTensor.word_grade,
  GUT.WeylHiggsFirstTensor.word_lorentz => Physics.WeylHiggsFirstTensor.word_lorentz
]

assert_compatible GUT.WeylHiggsFirstTensor.Dir => Physics.WeylHiggsFirstTensor.Dir
assert_compatible GUT.WeylHiggsFirstTensor.Spin => Physics.WeylHiggsFirstTensor.Spin
assert_compatible GUT.WeylHiggsFirstTensor.directional_covariant => Physics.WeylHiggsFirstTensor.directional_covariant
assert_compatible GUT.WeylHiggsFirstTensor.directional_grade => Physics.WeylHiggsFirstTensor.directional_grade
assert_compatible GUT.WeylHiggsFirstTensor.evenField => Physics.WeylHiggsFirstTensor.evenField
assert_compatible GUT.WeylHiggsFirstTensor.even_lorentz => Physics.WeylHiggsFirstTensor.even_lorentz
assert_compatible GUT.WeylHiggsFirstTensor.instAddCommGroupA_physics => Physics.WeylHiggsFirstTensor.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsFirstTensor.instModuleComplexA_physics => Physics.WeylHiggsFirstTensor.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsFirstTensor.instRingA_physics => Physics.WeylHiggsFirstTensor.instRingA_physics
assert_compatible GUT.WeylHiggsFirstTensor.oddField => Physics.WeylHiggsFirstTensor.oddField
assert_compatible GUT.WeylHiggsFirstTensor.oddField.eq_1 => Physics.WeylHiggsFirstTensor.oddField.eq_1
assert_compatible GUT.WeylHiggsFirstTensor.oddField_grade => Physics.WeylHiggsFirstTensor.oddField_grade
assert_compatible GUT.WeylHiggsFirstTensor.oddField_single => Physics.WeylHiggsFirstTensor.oddField_single
assert_compatible GUT.WeylHiggsFirstTensor.odd_lorentz => Physics.WeylHiggsFirstTensor.odd_lorentz
assert_compatible GUT.WeylHiggsFirstTensor.rest => Physics.WeylHiggsFirstTensor.rest
assert_compatible GUT.WeylHiggsFirstTensor.rest.eq_1 => Physics.WeylHiggsFirstTensor.rest.eq_1
assert_compatible GUT.WeylHiggsFirstTensor.rest_lorentz => Physics.WeylHiggsFirstTensor.rest_lorentz
assert_compatible GUT.WeylHiggsFirstTensor.tensor => Physics.WeylHiggsFirstTensor.tensor
assert_compatible GUT.WeylHiggsFirstTensor.tensor_apply => Physics.WeylHiggsFirstTensor.tensor_apply
assert_compatible GUT.WeylHiggsFirstTensor.tensor_invariant => Physics.WeylHiggsFirstTensor.tensor_invariant
assert_compatible GUT.WeylHiggsFirstTensor.transport => Physics.WeylHiggsFirstTensor.transport
assert_compatible GUT.WeylHiggsFirstTensor.transport_apply => Physics.WeylHiggsFirstTensor.transport_apply
assert_compatible GUT.WeylHiggsFirstTensor.word => Physics.WeylHiggsFirstTensor.word
assert_compatible GUT.WeylHiggsFirstTensor.word_grade => Physics.WeylHiggsFirstTensor.word_grade
assert_compatible GUT.WeylHiggsFirstTensor.word_lorentz => Physics.WeylHiggsFirstTensor.word_lorentz
