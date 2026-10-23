import Physics.StandardModel.Operators.Weinberg.BgwChargedHiggsWeinberg
import Physics.StandardModel.Operators.BgwZ6Selection
import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.BgwChargedHiggsWeinberg instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BgwChargedHiggsWeinberg.H => Physics.BgwChargedHiggsWeinberg.H,
  GUT.BgwChargedHiggsWeinberg.Sector => Physics.BgwChargedHiggsWeinberg.Sector,
  GUT.BgwChargedHiggsWeinberg.actualDomain => Physics.BgwChargedHiggsWeinberg.actualDomain,
  GUT.BgwChargedHiggsWeinberg.actualH => Physics.BgwChargedHiggsWeinberg.actualH,
  GUT.BgwChargedHiggsWeinberg.actualL => Physics.BgwChargedHiggsWeinberg.actualL,
  GUT.BgwChargedHiggsWeinberg.coefficientEquiv => Physics.BgwChargedHiggsWeinberg.coefficientEquiv,
  GUT.BgwChargedHiggsWeinberg.domainEquiv => Physics.BgwChargedHiggsWeinberg.domainEquiv,
  GUT.BgwChargedHiggsWeinberg.exists_nonzero => Physics.BgwChargedHiggsWeinberg.exists_nonzero,
  GUT.BgwChargedHiggsWeinberg.higgsEquiv => Physics.BgwChargedHiggsWeinberg.higgsEquiv,
  GUT.BgwChargedHiggsWeinberg.higgs_scalar => Physics.BgwChargedHiggsWeinberg.higgs_scalar,
  GUT.BgwChargedHiggsWeinberg.instAddCommGroupLeptonComplex => Physics.BgwChargedHiggsWeinberg.instAddCommGroupLeptonComplex,
  GUT.BgwChargedHiggsWeinberg.instAddCommGroupScalarFieldComplexOfNatScalarSpecies => Physics.BgwChargedHiggsWeinberg.instAddCommGroupScalarFieldComplexOfNatScalarSpecies,
  GUT.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinScalarFieldScalarSpecies => Physics.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinScalarFieldScalarSpecies,
  GUT.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexWeakSpace => Physics.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexWeakSpace,
  GUT.BgwChargedHiggsWeinberg.leptonEquiv => Physics.BgwChargedHiggsWeinberg.leptonEquiv,
  GUT.BgwChargedHiggsWeinberg.lepton_scalar => Physics.BgwChargedHiggsWeinberg.lepton_scalar,
  GUT.BgwChargedHiggsWeinberg.neutralDomain => Physics.BgwChargedHiggsWeinberg.neutralDomain,
  GUT.BgwChargedHiggsWeinberg.neutralEquiv => Physics.BgwChargedHiggsWeinberg.neutralEquiv,
  GUT.BgwChargedHiggsWeinberg.neutralFlavor => Physics.BgwChargedHiggsWeinberg.neutralFlavor,
  GUT.BgwChargedHiggsWeinberg.neutralH => Physics.BgwChargedHiggsWeinberg.neutralH,
  GUT.BgwChargedHiggsWeinberg.neutralL => Physics.BgwChargedHiggsWeinberg.neutralL,
  GUT.BgwChargedHiggsWeinberg.phase => Physics.BgwChargedHiggsWeinberg.phase,
  GUT.BgwChargedHiggsWeinberg.phase.eq_1 => Physics.BgwChargedHiggsWeinberg.phase.eq_1,
  GUT.BgwChargedHiggsWeinberg.phases => Physics.BgwChargedHiggsWeinberg.phases,
  GUT.BgwChargedHiggsWeinberg.witness => Physics.BgwChargedHiggsWeinberg.witness,
  GUT.BgwChargedHiggsWeinberg.witness.eq_1 => Physics.BgwChargedHiggsWeinberg.witness.eq_1,
  GUT.BgwChargedHiggsWeinberg.witness_coordinate => Physics.BgwChargedHiggsWeinberg.witness_coordinate,
  GUT.BgwChargedHiggsWeinberg.witness_nonzero => Physics.BgwChargedHiggsWeinberg.witness_nonzero,
  GUT.BnvMixedInput.scalarGauge.eq_1 => Physics.BnvMixedInput.scalarGauge.eq_1,
  GUT.BnvMixedInput.scalarGauge.eq_2 => Physics.BnvMixedInput.scalarGauge.eq_2,
  GUT.WeinbergSMInterface.lepton.eq_1 => Physics.WeinbergSMInterface.lepton.eq_1
]

assert_compatible GUT.BgwChargedHiggsWeinberg.H => Physics.BgwChargedHiggsWeinberg.H
assert_compatible GUT.BgwChargedHiggsWeinberg.Sector => Physics.BgwChargedHiggsWeinberg.Sector
assert_compatible GUT.BgwChargedHiggsWeinberg.actualDomain => Physics.BgwChargedHiggsWeinberg.actualDomain
assert_compatible GUT.BgwChargedHiggsWeinberg.actualH => Physics.BgwChargedHiggsWeinberg.actualH
assert_compatible GUT.BgwChargedHiggsWeinberg.actualL => Physics.BgwChargedHiggsWeinberg.actualL
assert_compatible GUT.BgwChargedHiggsWeinberg.coefficientEquiv => Physics.BgwChargedHiggsWeinberg.coefficientEquiv
assert_compatible GUT.BgwChargedHiggsWeinberg.domainEquiv => Physics.BgwChargedHiggsWeinberg.domainEquiv
assert_compatible GUT.BgwChargedHiggsWeinberg.exists_nonzero => Physics.BgwChargedHiggsWeinberg.exists_nonzero
assert_compatible GUT.BgwChargedHiggsWeinberg.higgsEquiv => Physics.BgwChargedHiggsWeinberg.higgsEquiv
assert_compatible GUT.BgwChargedHiggsWeinberg.higgs_scalar => Physics.BgwChargedHiggsWeinberg.higgs_scalar
assert_compatible GUT.BgwChargedHiggsWeinberg.instAddCommGroupLeptonComplex => Physics.BgwChargedHiggsWeinberg.instAddCommGroupLeptonComplex
assert_compatible GUT.BgwChargedHiggsWeinberg.instAddCommGroupScalarFieldComplexOfNatScalarSpecies => Physics.BgwChargedHiggsWeinberg.instAddCommGroupScalarFieldComplexOfNatScalarSpecies
assert_compatible GUT.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinScalarFieldScalarSpecies => Physics.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexSubtypeExteriorAlgebraLeptonMemSubmoduleExteriorPowerOfNatNatSymmetricPowerFinScalarFieldScalarSpecies
assert_compatible GUT.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexWeakSpace => Physics.BgwChargedHiggsWeinberg.instAddCommGroupTensorProductComplexWeakSpace
assert_compatible GUT.BgwChargedHiggsWeinberg.leptonEquiv => Physics.BgwChargedHiggsWeinberg.leptonEquiv
assert_compatible GUT.BgwChargedHiggsWeinberg.lepton_scalar => Physics.BgwChargedHiggsWeinberg.lepton_scalar
assert_compatible GUT.BgwChargedHiggsWeinberg.neutralDomain => Physics.BgwChargedHiggsWeinberg.neutralDomain
assert_compatible GUT.BgwChargedHiggsWeinberg.neutralEquiv => Physics.BgwChargedHiggsWeinberg.neutralEquiv
assert_compatible GUT.BgwChargedHiggsWeinberg.neutralFlavor => Physics.BgwChargedHiggsWeinberg.neutralFlavor
assert_compatible GUT.BgwChargedHiggsWeinberg.neutralH => Physics.BgwChargedHiggsWeinberg.neutralH
assert_compatible GUT.BgwChargedHiggsWeinberg.neutralL => Physics.BgwChargedHiggsWeinberg.neutralL
assert_compatible GUT.BgwChargedHiggsWeinberg.phase => Physics.BgwChargedHiggsWeinberg.phase
assert_compatible GUT.BgwChargedHiggsWeinberg.phase.eq_1 => Physics.BgwChargedHiggsWeinberg.phase.eq_1
assert_compatible GUT.BgwChargedHiggsWeinberg.phases => Physics.BgwChargedHiggsWeinberg.phases
assert_compatible GUT.BgwChargedHiggsWeinberg.witness => Physics.BgwChargedHiggsWeinberg.witness
assert_compatible GUT.BgwChargedHiggsWeinberg.witness.eq_1 => Physics.BgwChargedHiggsWeinberg.witness.eq_1
assert_compatible GUT.BgwChargedHiggsWeinberg.witness_coordinate => Physics.BgwChargedHiggsWeinberg.witness_coordinate
assert_compatible GUT.BgwChargedHiggsWeinberg.witness_nonzero => Physics.BgwChargedHiggsWeinberg.witness_nonzero
assert_compatible GUT.BnvMixedInput.scalarGauge.eq_1 => Physics.BnvMixedInput.scalarGauge.eq_1
assert_compatible GUT.BnvMixedInput.scalarGauge.eq_2 => Physics.BnvMixedInput.scalarGauge.eq_2
assert_compatible GUT.WeinbergSMInterface.lepton.eq_1 => Physics.WeinbergSMInterface.lepton.eq_1
