import Physics.FieldTheory.Mass.Surplus.CommonCopyKernel
import Physics.FieldTheory.Mass.EquivariantMassIndex
import Physics.StandardModel.Operators.QqueSpinorExterior
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.CommonCopyKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CommonCopyKernel.Family => Physics.CommonCopyKernel.Family,
  GUT.CommonCopyKernel.TargetCopy => Physics.CommonCopyKernel.TargetCopy,
  GUT.CommonCopyKernel.difference => Physics.CommonCopyKernel.difference,
  GUT.CommonCopyKernel.difference.eq_1 => Physics.CommonCopyKernel.difference.eq_1,
  GUT.CommonCopyKernel.difference_character => Physics.CommonCopyKernel.difference_character,
  GUT.CommonCopyKernel.difference_dimension => Physics.CommonCopyKernel.difference_dimension,
  GUT.CommonCopyKernel.exists_common_split => Physics.CommonCopyKernel.exists_common_split,
  GUT.CommonCopyKernel.exists_common_split_of_continuous => Physics.CommonCopyKernel.exists_common_split_of_continuous,
  GUT.CommonCopyKernel.familyAction => Physics.CommonCopyKernel.familyAction,
  GUT.CommonCopyKernel.familyFinite => Physics.CommonCopyKernel.familyFinite,
  GUT.CommonCopyKernel.familyNormedAdd => Physics.CommonCopyKernel.familyNormedAdd,
  GUT.CommonCopyKernel.familyNormedSpace => Physics.CommonCopyKernel.familyNormedSpace,
  GUT.CommonCopyKernel.kernelEquiv => Physics.CommonCopyKernel.kernelEquiv,
  GUT.CommonCopyKernel.kernel_difference => Physics.CommonCopyKernel.kernel_difference,
  GUT.CommonCopyKernel.kernel_physical_exterior => Physics.CommonCopyKernel.kernel_physical_exterior,
  GUT.CommonCopyKernel.kernel_physical_exterior_of_continuous => Physics.CommonCopyKernel.kernel_physical_exterior_of_continuous,
  GUT.CommonCopyKernel.leftover => Physics.CommonCopyKernel.leftover,
  GUT.CommonCopyKernel.positive_kernel_split => Physics.CommonCopyKernel.positive_kernel_split,
  GUT.CommonCopyKernel.presentation => Physics.CommonCopyKernel.presentation,
  GUT.CommonCopyKernel.targetCoordinateContinuity => Physics.CommonCopyKernel.targetCoordinateContinuity,
  GUT.CommonCopyKernel.targetEquiv => Physics.CommonCopyKernel.targetEquiv,
  GUT.CommonCopyKernel.transportMass => Physics.CommonCopyKernel.transportMass,
  GUT.CommonCopyKernel.unitaryTarget => Physics.CommonCopyKernel.unitaryTarget,
  GUT.CommonCopyKernel.unitaryTarget_continuous => Physics.CommonCopyKernel.unitaryTarget_continuous,
  GUT.CommonCopyKernel.unitaryTarget_unitary => Physics.CommonCopyKernel.unitaryTarget_unitary
]

assert_compatible GUT.CommonCopyKernel.Family => Physics.CommonCopyKernel.Family
assert_compatible GUT.CommonCopyKernel.TargetCopy => Physics.CommonCopyKernel.TargetCopy
assert_compatible GUT.CommonCopyKernel.difference => Physics.CommonCopyKernel.difference
assert_compatible GUT.CommonCopyKernel.difference.eq_1 => Physics.CommonCopyKernel.difference.eq_1
assert_compatible GUT.CommonCopyKernel.difference_character => Physics.CommonCopyKernel.difference_character
assert_compatible GUT.CommonCopyKernel.difference_dimension => Physics.CommonCopyKernel.difference_dimension
assert_compatible GUT.CommonCopyKernel.exists_common_split => Physics.CommonCopyKernel.exists_common_split
assert_compatible GUT.CommonCopyKernel.exists_common_split_of_continuous => Physics.CommonCopyKernel.exists_common_split_of_continuous
assert_compatible GUT.CommonCopyKernel.familyAction => Physics.CommonCopyKernel.familyAction
assert_compatible GUT.CommonCopyKernel.familyFinite => Physics.CommonCopyKernel.familyFinite
assert_compatible GUT.CommonCopyKernel.familyNormedAdd => Physics.CommonCopyKernel.familyNormedAdd
assert_compatible GUT.CommonCopyKernel.familyNormedSpace => Physics.CommonCopyKernel.familyNormedSpace
assert_compatible GUT.CommonCopyKernel.kernelEquiv => Physics.CommonCopyKernel.kernelEquiv
assert_compatible GUT.CommonCopyKernel.kernel_difference => Physics.CommonCopyKernel.kernel_difference
assert_compatible GUT.CommonCopyKernel.kernel_physical_exterior => Physics.CommonCopyKernel.kernel_physical_exterior
assert_compatible GUT.CommonCopyKernel.kernel_physical_exterior_of_continuous => Physics.CommonCopyKernel.kernel_physical_exterior_of_continuous
assert_compatible GUT.CommonCopyKernel.leftover => Physics.CommonCopyKernel.leftover
assert_compatible GUT.CommonCopyKernel.positive_kernel_split => Physics.CommonCopyKernel.positive_kernel_split
assert_compatible GUT.CommonCopyKernel.presentation => Physics.CommonCopyKernel.presentation
assert_compatible GUT.CommonCopyKernel.targetCoordinateContinuity => Physics.CommonCopyKernel.targetCoordinateContinuity
assert_compatible GUT.CommonCopyKernel.targetEquiv => Physics.CommonCopyKernel.targetEquiv
assert_compatible GUT.CommonCopyKernel.transportMass => Physics.CommonCopyKernel.transportMass
assert_compatible GUT.CommonCopyKernel.unitaryTarget => Physics.CommonCopyKernel.unitaryTarget
assert_compatible GUT.CommonCopyKernel.unitaryTarget_continuous => Physics.CommonCopyKernel.unitaryTarget_continuous
assert_compatible GUT.CommonCopyKernel.unitaryTarget_unitary => Physics.CommonCopyKernel.unitaryTarget_unitary
