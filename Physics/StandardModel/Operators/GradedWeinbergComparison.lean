import Physics.StandardModel.Operators.Weinberg.GradedWeinbergComparison
import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.RepresentationTheory.TypedMixedSeparatedHom
import Math.LinearAlgebra.LinearEquivComparison
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.GradedWeinbergComparison instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.GradedWeinbergComparison.LocalGroup => Physics.GradedWeinbergComparison.LocalGroup,
  GUT.GradedWeinbergComparison.Residual => Physics.GradedWeinbergComparison.Residual,
  GUT.GradedWeinbergComparison.boson => Physics.GradedWeinbergComparison.boson,
  GUT.GradedWeinbergComparison.comparison => Physics.GradedWeinbergComparison.comparison,
  GUT.GradedWeinbergComparison.domainEquiv => Physics.GradedWeinbergComparison.domainEquiv,
  GUT.GradedWeinbergComparison.domainEquiv_pure => Physics.GradedWeinbergComparison.domainEquiv_pure,
  GUT.GradedWeinbergComparison.equiv => Physics.GradedWeinbergComparison.equiv,
  GUT.GradedWeinbergComparison.extract_reconstruct => Physics.GradedWeinbergComparison.extract_reconstruct,
  GUT.GradedWeinbergComparison.extraction_commutes => Physics.GradedWeinbergComparison.extraction_commutes,
  GUT.GradedWeinbergComparison.fermion => Physics.GradedWeinbergComparison.fermion,
  GUT.GradedWeinbergComparison.flavor => Physics.GradedWeinbergComparison.flavor,
  GUT.GradedWeinbergComparison.flavor.eq_1 => Physics.GradedWeinbergComparison.flavor.eq_1,
  GUT.GradedWeinbergComparison.forbidden_iff => Physics.GradedWeinbergComparison.forbidden_iff,
  GUT.GradedWeinbergComparison.higgsEquiv => Physics.GradedWeinbergComparison.higgsEquiv,
  GUT.GradedWeinbergComparison.inputEquiv => Physics.GradedWeinbergComparison.inputEquiv,
  GUT.GradedWeinbergComparison.inputEquiv_pure => Physics.GradedWeinbergComparison.inputEquiv_pure,
  GUT.GradedWeinbergComparison.instAddCommGroupLepton => Physics.GradedWeinbergComparison.instAddCommGroupLepton,
  GUT.GradedWeinbergComparison.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak => Physics.GradedWeinbergComparison.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak,
  GUT.GradedWeinbergComparison.instAddCommGroupTensorProductComplexWeakSpace => Physics.GradedWeinbergComparison.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.GradedWeinbergComparison.leptonEquiv => Physics.GradedWeinbergComparison.leptonEquiv,
  GUT.GradedWeinbergComparison.localHiggs => Physics.GradedWeinbergComparison.localHiggs,
  GUT.GradedWeinbergComparison.localHiggs.eq_1 => Physics.GradedWeinbergComparison.localHiggs.eq_1,
  GUT.GradedWeinbergComparison.localLepton => Physics.GradedWeinbergComparison.localLepton,
  GUT.GradedWeinbergComparison.localLepton.eq_1 => Physics.GradedWeinbergComparison.localLepton.eq_1,
  GUT.GradedWeinbergComparison.nonzero_iff => Physics.GradedWeinbergComparison.nonzero_iff,
  GUT.GradedWeinbergComparison.onSMEquiv => Physics.GradedWeinbergComparison.onSMEquiv,
  GUT.GradedWeinbergComparison.onSMEquiv_def => Physics.GradedWeinbergComparison.onSMEquiv_def,
  GUT.GradedWeinbergComparison.oneGenerationEquiv => Physics.GradedWeinbergComparison.oneGenerationEquiv,
  GUT.GradedWeinbergComparison.pattern => Physics.GradedWeinbergComparison.pattern,
  GUT.GradedWeinbergComparison.reconstruct_extract => Physics.GradedWeinbergComparison.reconstruct_extract,
  GUT.GradedWeinbergComparison.reconstruction_commutes => Physics.GradedWeinbergComparison.reconstruction_commutes,
  GUT.GradedWeinbergComparison.scalarFlavor => Physics.GradedWeinbergComparison.scalarFlavor,
  GUT.GradedWeinbergComparison.scalarFlavor.eq_1 => Physics.GradedWeinbergComparison.scalarFlavor.eq_1,
  GUT.WeinbergModelSector.higgs.eq_1 => Physics.WeinbergModelSector.higgs.eq_1,
  GUT.WeinbergModelSector.lepton.eq_1 => Physics.WeinbergModelSector.lepton.eq_1
]

assert_compatible GUT.GradedWeinbergComparison.LocalGroup => Physics.GradedWeinbergComparison.LocalGroup
assert_compatible GUT.GradedWeinbergComparison.Residual => Physics.GradedWeinbergComparison.Residual
assert_compatible GUT.GradedWeinbergComparison.boson => Physics.GradedWeinbergComparison.boson
assert_compatible GUT.GradedWeinbergComparison.comparison => Physics.GradedWeinbergComparison.comparison
assert_compatible GUT.GradedWeinbergComparison.domainEquiv => Physics.GradedWeinbergComparison.domainEquiv
assert_compatible GUT.GradedWeinbergComparison.domainEquiv_pure => Physics.GradedWeinbergComparison.domainEquiv_pure
assert_compatible GUT.GradedWeinbergComparison.equiv => Physics.GradedWeinbergComparison.equiv
assert_compatible GUT.GradedWeinbergComparison.extract_reconstruct => Physics.GradedWeinbergComparison.extract_reconstruct
assert_compatible GUT.GradedWeinbergComparison.extraction_commutes => Physics.GradedWeinbergComparison.extraction_commutes
assert_compatible GUT.GradedWeinbergComparison.fermion => Physics.GradedWeinbergComparison.fermion
assert_compatible GUT.GradedWeinbergComparison.flavor => Physics.GradedWeinbergComparison.flavor
assert_compatible GUT.GradedWeinbergComparison.flavor.eq_1 => Physics.GradedWeinbergComparison.flavor.eq_1
assert_compatible GUT.GradedWeinbergComparison.forbidden_iff => Physics.GradedWeinbergComparison.forbidden_iff
assert_compatible GUT.GradedWeinbergComparison.higgsEquiv => Physics.GradedWeinbergComparison.higgsEquiv
assert_compatible GUT.GradedWeinbergComparison.inputEquiv => Physics.GradedWeinbergComparison.inputEquiv
assert_compatible GUT.GradedWeinbergComparison.inputEquiv_pure => Physics.GradedWeinbergComparison.inputEquiv_pure
assert_compatible GUT.GradedWeinbergComparison.instAddCommGroupLepton => Physics.GradedWeinbergComparison.instAddCommGroupLepton
assert_compatible GUT.GradedWeinbergComparison.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak => Physics.GradedWeinbergComparison.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinWeak
assert_compatible GUT.GradedWeinbergComparison.instAddCommGroupTensorProductComplexWeakSpace => Physics.GradedWeinbergComparison.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.GradedWeinbergComparison.leptonEquiv => Physics.GradedWeinbergComparison.leptonEquiv
assert_compatible GUT.GradedWeinbergComparison.localHiggs => Physics.GradedWeinbergComparison.localHiggs
assert_compatible GUT.GradedWeinbergComparison.localHiggs.eq_1 => Physics.GradedWeinbergComparison.localHiggs.eq_1
assert_compatible GUT.GradedWeinbergComparison.localLepton => Physics.GradedWeinbergComparison.localLepton
assert_compatible GUT.GradedWeinbergComparison.localLepton.eq_1 => Physics.GradedWeinbergComparison.localLepton.eq_1
assert_compatible GUT.GradedWeinbergComparison.nonzero_iff => Physics.GradedWeinbergComparison.nonzero_iff
assert_compatible GUT.GradedWeinbergComparison.onSMEquiv => Physics.GradedWeinbergComparison.onSMEquiv
assert_compatible GUT.GradedWeinbergComparison.onSMEquiv_def => Physics.GradedWeinbergComparison.onSMEquiv_def
assert_compatible GUT.GradedWeinbergComparison.oneGenerationEquiv => Physics.GradedWeinbergComparison.oneGenerationEquiv
assert_compatible GUT.GradedWeinbergComparison.pattern => Physics.GradedWeinbergComparison.pattern
assert_compatible GUT.GradedWeinbergComparison.reconstruct_extract => Physics.GradedWeinbergComparison.reconstruct_extract
assert_compatible GUT.GradedWeinbergComparison.reconstruction_commutes => Physics.GradedWeinbergComparison.reconstruction_commutes
assert_compatible GUT.GradedWeinbergComparison.scalarFlavor => Physics.GradedWeinbergComparison.scalarFlavor
assert_compatible GUT.GradedWeinbergComparison.scalarFlavor.eq_1 => Physics.GradedWeinbergComparison.scalarFlavor.eq_1
assert_compatible GUT.WeinbergModelSector.higgs.eq_1 => Physics.WeinbergModelSector.higgs.eq_1
assert_compatible GUT.WeinbergModelSector.lepton.eq_1 => Physics.WeinbergModelSector.lepton.eq_1
