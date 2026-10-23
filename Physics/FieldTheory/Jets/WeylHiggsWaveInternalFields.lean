import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInternalFields
import Physics.FieldTheory.Jets.WeylHiggsWaveMoments
import Math.Algebra.ColoredFirstJetFields
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInternalFields instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveInternalFields.Fields => Physics.WeylHiggsWaveInternalFields.Fields,
  GUT.WeylHiggsWaveInternalFields.amplitude => Physics.WeylHiggsWaveInternalFields.amplitude,
  GUT.WeylHiggsWaveInternalFields.amplitude.eq_1 => Physics.WeylHiggsWaveInternalFields.amplitude.eq_1,
  GUT.WeylHiggsWaveInternalFields.fieldTensor => Physics.WeylHiggsWaveInternalFields.fieldTensor,
  GUT.WeylHiggsWaveInternalFields.fieldTensor.eq_1 => Physics.WeylHiggsWaveInternalFields.fieldTensor.eq_1,
  GUT.WeylHiggsWaveInternalFields.fieldTensor_model => Physics.WeylHiggsWaveInternalFields.fieldTensor_model,
  GUT.WeylHiggsWaveInternalFields.first_covariant => Physics.WeylHiggsWaveInternalFields.first_covariant,
  GUT.WeylHiggsWaveInternalFields.instAddCommGroupA_physics => Physics.WeylHiggsWaveInternalFields.instAddCommGroupA_physics,
  GUT.WeylHiggsWaveInternalFields.instModuleComplexA_physics => Physics.WeylHiggsWaveInternalFields.instModuleComplexA_physics,
  GUT.WeylHiggsWaveInternalFields.instRingA_physics => Physics.WeylHiggsWaveInternalFields.instRingA_physics,
  GUT.WeylHiggsWaveInternalFields.onScalar => Physics.WeylHiggsWaveInternalFields.onScalar,
  GUT.WeylHiggsWaveInternalFields.onScalar_apply => Physics.WeylHiggsWaveInternalFields.onScalar_apply,
  GUT.WeylHiggsWaveInternalFields.scalar_invariant => Physics.WeylHiggsWaveInternalFields.scalar_invariant
]

assert_compatible GUT.WeylHiggsWaveInternalFields.Fields => Physics.WeylHiggsWaveInternalFields.Fields
assert_compatible GUT.WeylHiggsWaveInternalFields.amplitude => Physics.WeylHiggsWaveInternalFields.amplitude
assert_compatible GUT.WeylHiggsWaveInternalFields.amplitude.eq_1 => Physics.WeylHiggsWaveInternalFields.amplitude.eq_1
assert_compatible GUT.WeylHiggsWaveInternalFields.fieldTensor => Physics.WeylHiggsWaveInternalFields.fieldTensor
assert_compatible GUT.WeylHiggsWaveInternalFields.fieldTensor.eq_1 => Physics.WeylHiggsWaveInternalFields.fieldTensor.eq_1
assert_compatible GUT.WeylHiggsWaveInternalFields.fieldTensor_model => Physics.WeylHiggsWaveInternalFields.fieldTensor_model
assert_compatible GUT.WeylHiggsWaveInternalFields.first_covariant => Physics.WeylHiggsWaveInternalFields.first_covariant
assert_compatible GUT.WeylHiggsWaveInternalFields.instAddCommGroupA_physics => Physics.WeylHiggsWaveInternalFields.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsWaveInternalFields.instModuleComplexA_physics => Physics.WeylHiggsWaveInternalFields.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsWaveInternalFields.instRingA_physics => Physics.WeylHiggsWaveInternalFields.instRingA_physics
assert_compatible GUT.WeylHiggsWaveInternalFields.onScalar => Physics.WeylHiggsWaveInternalFields.onScalar
assert_compatible GUT.WeylHiggsWaveInternalFields.onScalar_apply => Physics.WeylHiggsWaveInternalFields.onScalar_apply
assert_compatible GUT.WeylHiggsWaveInternalFields.scalar_invariant => Physics.WeylHiggsWaveInternalFields.scalar_invariant
