import Physics.StandardModel.Operators.Weinberg.WeinbergGrading
import Physics.StandardModel.Operators.WeinbergSMInterface
import Physics.StandardModel.Operators.StandardModelLocalOperator
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.WeinbergGrading instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeinbergGrading.conjugate_lepton_scaling => Physics.WeinbergGrading.conjugate_lepton_scaling,
  GUT.WeinbergGrading.instAddCommGroupLepton => Physics.WeinbergGrading.instAddCommGroupLepton,
  GUT.WeinbergGrading.instAddCommGroupTensorProductComplexWeakSpace => Physics.WeinbergGrading.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.WeinbergGrading.lepton_scaling => Physics.WeinbergGrading.lepton_scaling,
  GUT.WeinbergGrading.quantumNumbers => Physics.WeinbergGrading.quantumNumbers,
  GUT.WeinbergGrading.signature => Physics.WeinbergGrading.signature,
  GUT.WeinbergGrading.slot_scaling => Physics.WeinbergGrading.slot_scaling
]

assert_compatible GUT.WeinbergGrading.conjugate_lepton_scaling => Physics.WeinbergGrading.conjugate_lepton_scaling
assert_compatible GUT.WeinbergGrading.instAddCommGroupLepton => Physics.WeinbergGrading.instAddCommGroupLepton
assert_compatible GUT.WeinbergGrading.instAddCommGroupTensorProductComplexWeakSpace => Physics.WeinbergGrading.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.WeinbergGrading.lepton_scaling => Physics.WeinbergGrading.lepton_scaling
assert_compatible GUT.WeinbergGrading.quantumNumbers => Physics.WeinbergGrading.quantumNumbers
assert_compatible GUT.WeinbergGrading.signature => Physics.WeinbergGrading.signature
assert_compatible GUT.WeinbergGrading.slot_scaling => Physics.WeinbergGrading.slot_scaling
