import Physics.FieldTheory.Jets.Weyl.Equations.WeylSingleFieldIBP
import Physics.FieldTheory.Jets.WeylEquationIBP
import Math.Algebra.LinearJetSingleField
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylSingleFieldIBP instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylSingleFieldIBP.Quotient => Physics.WeylSingleFieldIBP.Quotient,
  GUT.WeylSingleFieldIBP.Relations => Physics.WeylSingleFieldIBP.Relations,
  GUT.WeylSingleFieldIBP.Source => Physics.WeylSingleFieldIBP.Source,
  GUT.WeylSingleFieldIBP.action => Physics.WeylSingleFieldIBP.action,
  GUT.WeylSingleFieldIBP.basis => Physics.WeylSingleFieldIBP.basis,
  GUT.WeylSingleFieldIBP.coefficient_zero => Physics.WeylSingleFieldIBP.coefficient_zero,
  GUT.WeylSingleFieldIBP.dimension => Physics.WeylSingleFieldIBP.dimension,
  GUT.WeylSingleFieldIBP.firstJet => Physics.WeylSingleFieldIBP.firstJet,
  GUT.WeylSingleFieldIBP.firstJet_ibp_zero => Physics.WeylSingleFieldIBP.firstJet_ibp_zero,
  GUT.WeylSingleFieldIBP.firstJet_nonzero => Physics.WeylSingleFieldIBP.firstJet_nonzero,
  GUT.WeylSingleFieldIBP.instAddCommGroupSubtypeAlgebraFinOfNatNatUnitEquationsComplexSeedSpectatorSeedMemSubmoduleSource => Physics.WeylSingleFieldIBP.instAddCommGroupSubtypeAlgebraFinOfNatNatUnitEquationsComplexSeedSpectatorSeedMemSubmoduleSource,
  GUT.WeylSingleFieldIBP.instModuleComplexSubtypeAlgebraFinOfNatNatUnitEquationsSeedSpectatorSeedMemSubmoduleSource => Physics.WeylSingleFieldIBP.instModuleComplexSubtypeAlgebraFinOfNatNatUnitEquationsSeedSpectatorSeedMemSubmoduleSource,
  GUT.WeylSingleFieldIBP.quotient_zero => Physics.WeylSingleFieldIBP.quotient_zero,
  GUT.WeylSingleFieldIBP.relations_top => Physics.WeylSingleFieldIBP.relations_top
]

assert_compatible GUT.WeylSingleFieldIBP.Quotient => Physics.WeylSingleFieldIBP.Quotient
assert_compatible GUT.WeylSingleFieldIBP.Relations => Physics.WeylSingleFieldIBP.Relations
assert_compatible GUT.WeylSingleFieldIBP.Source => Physics.WeylSingleFieldIBP.Source
assert_compatible GUT.WeylSingleFieldIBP.action => Physics.WeylSingleFieldIBP.action
assert_compatible GUT.WeylSingleFieldIBP.basis => Physics.WeylSingleFieldIBP.basis
assert_compatible GUT.WeylSingleFieldIBP.coefficient_zero => Physics.WeylSingleFieldIBP.coefficient_zero
assert_compatible GUT.WeylSingleFieldIBP.dimension => Physics.WeylSingleFieldIBP.dimension
assert_compatible GUT.WeylSingleFieldIBP.firstJet => Physics.WeylSingleFieldIBP.firstJet
assert_compatible GUT.WeylSingleFieldIBP.firstJet_ibp_zero => Physics.WeylSingleFieldIBP.firstJet_ibp_zero
assert_compatible GUT.WeylSingleFieldIBP.firstJet_nonzero => Physics.WeylSingleFieldIBP.firstJet_nonzero
assert_compatible GUT.WeylSingleFieldIBP.instAddCommGroupSubtypeAlgebraFinOfNatNatUnitEquationsComplexSeedSpectatorSeedMemSubmoduleSource => Physics.WeylSingleFieldIBP.instAddCommGroupSubtypeAlgebraFinOfNatNatUnitEquationsComplexSeedSpectatorSeedMemSubmoduleSource
assert_compatible GUT.WeylSingleFieldIBP.instModuleComplexSubtypeAlgebraFinOfNatNatUnitEquationsSeedSpectatorSeedMemSubmoduleSource => Physics.WeylSingleFieldIBP.instModuleComplexSubtypeAlgebraFinOfNatNatUnitEquationsSeedSpectatorSeedMemSubmoduleSource
assert_compatible GUT.WeylSingleFieldIBP.quotient_zero => Physics.WeylSingleFieldIBP.quotient_zero
assert_compatible GUT.WeylSingleFieldIBP.relations_top => Physics.WeylSingleFieldIBP.relations_top
