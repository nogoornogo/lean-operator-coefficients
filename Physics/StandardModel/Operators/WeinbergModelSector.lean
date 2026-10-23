import Physics.StandardModel.Operators.Weinberg.WeinbergModelSector
import Physics.StandardModel.Operators.WeinbergResidualHom
import Physics.StandardModel.Operators.WeinbergPermutationCompleteness
import Math.RepresentationTheory.ExteriorSquareTensorDescent
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.WeinbergModelSector instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeinbergModelSector.Lepton => Physics.WeinbergModelSector.Lepton,
  GUT.WeinbergModelSector.ModelSector => Physics.WeinbergModelSector.ModelSector,
  GUT.WeinbergModelSector.ReducedGroup => Physics.WeinbergModelSector.ReducedGroup,
  GUT.WeinbergModelSector.TensorSector => Physics.WeinbergModelSector.TensorSector,
  GUT.WeinbergModelSector.higgs => Physics.WeinbergModelSector.higgs,
  GUT.WeinbergModelSector.homEquiv => Physics.WeinbergModelSector.homEquiv,
  GUT.WeinbergModelSector.homEquiv.eq_1 => Physics.WeinbergModelSector.homEquiv.eq_1,
  GUT.WeinbergModelSector.homEquiv_agrees => Physics.WeinbergModelSector.homEquiv_agrees,
  GUT.WeinbergModelSector.instAddCommGroupLepton => Physics.WeinbergModelSector.instAddCommGroupLepton,
  GUT.WeinbergModelSector.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak => Physics.WeinbergModelSector.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak,
  GUT.WeinbergModelSector.instAddCommGroupTensorProductComplexWeakSpace => Physics.WeinbergModelSector.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.WeinbergModelSector.inverse_agrees => Physics.WeinbergModelSector.inverse_agrees,
  GUT.WeinbergModelSector.lepton => Physics.WeinbergModelSector.lepton,
  GUT.WeinbergModelSector.orderedEquiv => Physics.WeinbergModelSector.orderedEquiv,
  GUT.WeinbergModelSector.orderedEquiv_apply => Physics.WeinbergModelSector.orderedEquiv_apply,
  GUT.WeinbergModelSector.regroup => Physics.WeinbergModelSector.regroup,
  GUT.WeinbergModelSector.regroupEquiv => Physics.WeinbergModelSector.regroupEquiv,
  GUT.WeinbergModelSector.regroup_apply => Physics.WeinbergModelSector.regroup_apply,
  GUT.WeinbergModelSector.sectorEquiv => Physics.WeinbergModelSector.sectorEquiv,
  GUT.WeinbergModelSector.sectorEquiv_apply => Physics.WeinbergModelSector.sectorEquiv_apply,
  GUT.WeinbergModelSector.statisticsEquiv => Physics.WeinbergModelSector.statisticsEquiv
]

assert_compatible GUT.WeinbergModelSector.Lepton => Physics.WeinbergModelSector.Lepton
assert_compatible GUT.WeinbergModelSector.ModelSector => Physics.WeinbergModelSector.ModelSector
assert_compatible GUT.WeinbergModelSector.ReducedGroup => Physics.WeinbergModelSector.ReducedGroup
assert_compatible GUT.WeinbergModelSector.TensorSector => Physics.WeinbergModelSector.TensorSector
assert_compatible GUT.WeinbergModelSector.higgs => Physics.WeinbergModelSector.higgs
assert_compatible GUT.WeinbergModelSector.homEquiv => Physics.WeinbergModelSector.homEquiv
assert_compatible GUT.WeinbergModelSector.homEquiv.eq_1 => Physics.WeinbergModelSector.homEquiv.eq_1
assert_compatible GUT.WeinbergModelSector.homEquiv_agrees => Physics.WeinbergModelSector.homEquiv_agrees
assert_compatible GUT.WeinbergModelSector.instAddCommGroupLepton => Physics.WeinbergModelSector.instAddCommGroupLepton
assert_compatible GUT.WeinbergModelSector.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak => Physics.WeinbergModelSector.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak
assert_compatible GUT.WeinbergModelSector.instAddCommGroupTensorProductComplexWeakSpace => Physics.WeinbergModelSector.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.WeinbergModelSector.inverse_agrees => Physics.WeinbergModelSector.inverse_agrees
assert_compatible GUT.WeinbergModelSector.lepton => Physics.WeinbergModelSector.lepton
assert_compatible GUT.WeinbergModelSector.orderedEquiv => Physics.WeinbergModelSector.orderedEquiv
assert_compatible GUT.WeinbergModelSector.orderedEquiv_apply => Physics.WeinbergModelSector.orderedEquiv_apply
assert_compatible GUT.WeinbergModelSector.regroup => Physics.WeinbergModelSector.regroup
assert_compatible GUT.WeinbergModelSector.regroupEquiv => Physics.WeinbergModelSector.regroupEquiv
assert_compatible GUT.WeinbergModelSector.regroup_apply => Physics.WeinbergModelSector.regroup_apply
assert_compatible GUT.WeinbergModelSector.sectorEquiv => Physics.WeinbergModelSector.sectorEquiv
assert_compatible GUT.WeinbergModelSector.sectorEquiv_apply => Physics.WeinbergModelSector.sectorEquiv_apply
assert_compatible GUT.WeinbergModelSector.statisticsEquiv => Physics.WeinbergModelSector.statisticsEquiv
