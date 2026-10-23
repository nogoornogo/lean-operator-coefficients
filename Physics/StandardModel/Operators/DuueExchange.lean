import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueExchange
import Physics.StandardModel.Operators.DuueOrderedCompleteness
import Math.RepresentationTheory.FourSlotCoefficientEquiv
import Math.LinearAlgebra.StatisticalCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueExchange instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuueExchange.Condition => Physics.DuueExchange.Condition,
  GUT.DuueExchange.OrderedSector => Physics.DuueExchange.OrderedSector,
  GUT.DuueExchange.Sector => Physics.DuueExchange.Sector,
  GUT.DuueExchange.antisymmetric_iff => Physics.DuueExchange.antisymmetric_iff,
  GUT.DuueExchange.antisymmetric_of_condition => Physics.DuueExchange.antisymmetric_of_condition,
  GUT.DuueExchange.condition_of_antisymmetric => Physics.DuueExchange.condition_of_antisymmetric,
  GUT.DuueExchange.exists_nonzero_iff => Physics.DuueExchange.exists_nonzero_iff,
  GUT.DuueExchange.exteriorEquiv => Physics.DuueExchange.exteriorEquiv,
  GUT.DuueExchange.instAddCommGroupTensorProductComplexColorSpace => Physics.DuueExchange.instAddCommGroupTensorProductComplexColorSpace,
  GUT.DuueExchange.instAddCommGroupTensorProductComplexColorSpace_1 => Physics.DuueExchange.instAddCommGroupTensorProductComplexColorSpace_1,
  GUT.DuueExchange.instAddCommGroupTensorProductComplexSpace => Physics.DuueExchange.instAddCommGroupTensorProductComplexSpace,
  GUT.DuueExchange.orderedEquiv => Physics.DuueExchange.orderedEquiv,
  GUT.DuueExchange.orderedEquiv_apply => Physics.DuueExchange.orderedEquiv_apply,
  GUT.DuueExchange.orderedEquiv_symm_apply => Physics.DuueExchange.orderedEquiv_symm_apply,
  GUT.DuueExchange.permutation_compatible => Physics.DuueExchange.permutation_compatible,
  GUT.DuueExchange.permutation_statistics_iff => Physics.DuueExchange.permutation_statistics_iff,
  GUT.DuueExchange.reconstruct_permutation => Physics.DuueExchange.reconstruct_permutation,
  GUT.DuueExchange.residualSpace => Physics.DuueExchange.residualSpace,
  GUT.DuueExchange.sourceAction => Physics.DuueExchange.sourceAction,
  GUT.DuueExchange.sourceAction.eq_1 => Physics.DuueExchange.sourceAction.eq_1,
  GUT.DuueExchange.targetAction => Physics.DuueExchange.targetAction,
  GUT.DuueExchange.targetAction.eq_1 => Physics.DuueExchange.targetAction.eq_1,
  GUT.DuueExchange.target_one => Physics.DuueExchange.target_one,
  GUT.DuueExchange.target_zero => Physics.DuueExchange.target_zero
]

assert_compatible GUT.DuueExchange.Condition => Physics.DuueExchange.Condition
assert_compatible GUT.DuueExchange.OrderedSector => Physics.DuueExchange.OrderedSector
assert_compatible GUT.DuueExchange.Sector => Physics.DuueExchange.Sector
assert_compatible GUT.DuueExchange.antisymmetric_iff => Physics.DuueExchange.antisymmetric_iff
assert_compatible GUT.DuueExchange.antisymmetric_of_condition => Physics.DuueExchange.antisymmetric_of_condition
assert_compatible GUT.DuueExchange.condition_of_antisymmetric => Physics.DuueExchange.condition_of_antisymmetric
assert_compatible GUT.DuueExchange.exists_nonzero_iff => Physics.DuueExchange.exists_nonzero_iff
assert_compatible GUT.DuueExchange.exteriorEquiv => Physics.DuueExchange.exteriorEquiv
assert_compatible GUT.DuueExchange.instAddCommGroupTensorProductComplexColorSpace => Physics.DuueExchange.instAddCommGroupTensorProductComplexColorSpace
assert_compatible GUT.DuueExchange.instAddCommGroupTensorProductComplexColorSpace_1 => Physics.DuueExchange.instAddCommGroupTensorProductComplexColorSpace_1
assert_compatible GUT.DuueExchange.instAddCommGroupTensorProductComplexSpace => Physics.DuueExchange.instAddCommGroupTensorProductComplexSpace
assert_compatible GUT.DuueExchange.orderedEquiv => Physics.DuueExchange.orderedEquiv
assert_compatible GUT.DuueExchange.orderedEquiv_apply => Physics.DuueExchange.orderedEquiv_apply
assert_compatible GUT.DuueExchange.orderedEquiv_symm_apply => Physics.DuueExchange.orderedEquiv_symm_apply
assert_compatible GUT.DuueExchange.permutation_compatible => Physics.DuueExchange.permutation_compatible
assert_compatible GUT.DuueExchange.permutation_statistics_iff => Physics.DuueExchange.permutation_statistics_iff
assert_compatible GUT.DuueExchange.reconstruct_permutation => Physics.DuueExchange.reconstruct_permutation
assert_compatible GUT.DuueExchange.residualSpace => Physics.DuueExchange.residualSpace
assert_compatible GUT.DuueExchange.sourceAction => Physics.DuueExchange.sourceAction
assert_compatible GUT.DuueExchange.sourceAction.eq_1 => Physics.DuueExchange.sourceAction.eq_1
assert_compatible GUT.DuueExchange.targetAction => Physics.DuueExchange.targetAction
assert_compatible GUT.DuueExchange.targetAction.eq_1 => Physics.DuueExchange.targetAction.eq_1
assert_compatible GUT.DuueExchange.target_one => Physics.DuueExchange.target_one
assert_compatible GUT.DuueExchange.target_zero => Physics.DuueExchange.target_zero
