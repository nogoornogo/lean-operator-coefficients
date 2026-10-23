import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInternalLift
import Physics.FieldTheory.Jets.WeylHiggsOddUpper
import Physics.FieldTheory.Jets.HiggsFirstInternal.Complete
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInternalLift instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.K.eq_1 => Physics.HiggsFirstInternal.K.eq_1,
  GUT.WeylHiggsInternalLift.even_scalar => Physics.WeylHiggsInternalLift.even_scalar,
  GUT.WeylHiggsInternalLift.even_word_scalar => Physics.WeylHiggsInternalLift.even_word_scalar,
  GUT.WeylHiggsInternalLift.instAddCommGroupA_physics => Physics.WeylHiggsInternalLift.instAddCommGroupA_physics,
  GUT.WeylHiggsInternalLift.instModuleComplexA_physics => Physics.WeylHiggsInternalLift.instModuleComplexA_physics,
  GUT.WeylHiggsInternalLift.instRingA_physics => Physics.WeylHiggsInternalLift.instRingA_physics,
  GUT.WeylHiggsInternalLift.labels => Physics.WeylHiggsInternalLift.labels,
  GUT.WeylHiggsInternalLift.mono_grade => Physics.WeylHiggsInternalLift.mono_grade,
  GUT.WeylHiggsInternalLift.mono_word => Physics.WeylHiggsInternalLift.mono_word,
  GUT.WeylHiggsInternalLift.paired_internal => Physics.WeylHiggsInternalLift.paired_internal,
  GUT.WeylHiggsInternalLift.primitive_internal => Physics.WeylHiggsInternalLift.primitive_internal,
  GUT.WeylHiggsInternalLift.rest_scalar => Physics.WeylHiggsInternalLift.rest_scalar,
  GUT.WeylHiggsInternalLift.scalarFunctional => Physics.WeylHiggsInternalLift.scalarFunctional,
  GUT.WeylHiggsInternalLift.scalarFunctional_apply => Physics.WeylHiggsInternalLift.scalarFunctional_apply,
  GUT.WeylHiggsInternalLift.scalar_coordinate => Physics.WeylHiggsInternalLift.scalar_coordinate,
  GUT.WeylHiggsInternalLift.scalar_internal => Physics.WeylHiggsInternalLift.scalar_internal,
  GUT.WeylHiggsInternalLift.scalar_invariant => Physics.WeylHiggsInternalLift.scalar_invariant
]

assert_compatible GUT.HiggsFirstInternal.K.eq_1 => Physics.HiggsFirstInternal.K.eq_1
assert_compatible GUT.WeylHiggsInternalLift.even_scalar => Physics.WeylHiggsInternalLift.even_scalar
assert_compatible GUT.WeylHiggsInternalLift.even_word_scalar => Physics.WeylHiggsInternalLift.even_word_scalar
assert_compatible GUT.WeylHiggsInternalLift.instAddCommGroupA_physics => Physics.WeylHiggsInternalLift.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsInternalLift.instModuleComplexA_physics => Physics.WeylHiggsInternalLift.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsInternalLift.instRingA_physics => Physics.WeylHiggsInternalLift.instRingA_physics
assert_compatible GUT.WeylHiggsInternalLift.labels => Physics.WeylHiggsInternalLift.labels
assert_compatible GUT.WeylHiggsInternalLift.mono_grade => Physics.WeylHiggsInternalLift.mono_grade
assert_compatible GUT.WeylHiggsInternalLift.mono_word => Physics.WeylHiggsInternalLift.mono_word
assert_compatible GUT.WeylHiggsInternalLift.paired_internal => Physics.WeylHiggsInternalLift.paired_internal
assert_compatible GUT.WeylHiggsInternalLift.primitive_internal => Physics.WeylHiggsInternalLift.primitive_internal
assert_compatible GUT.WeylHiggsInternalLift.rest_scalar => Physics.WeylHiggsInternalLift.rest_scalar
assert_compatible GUT.WeylHiggsInternalLift.scalarFunctional => Physics.WeylHiggsInternalLift.scalarFunctional
assert_compatible GUT.WeylHiggsInternalLift.scalarFunctional_apply => Physics.WeylHiggsInternalLift.scalarFunctional_apply
assert_compatible GUT.WeylHiggsInternalLift.scalar_coordinate => Physics.WeylHiggsInternalLift.scalar_coordinate
assert_compatible GUT.WeylHiggsInternalLift.scalar_internal => Physics.WeylHiggsInternalLift.scalar_internal
assert_compatible GUT.WeylHiggsInternalLift.scalar_invariant => Physics.WeylHiggsInternalLift.scalar_invariant
