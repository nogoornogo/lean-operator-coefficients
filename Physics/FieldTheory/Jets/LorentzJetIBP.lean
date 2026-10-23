import Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP
import Physics.FieldTheory.Jets.LorentzDirections
import Math.Algebra.JetSymbolEvaluation
import Math.RepresentationTheory.DirectionalJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lorentz.LorentzJetIBP instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzJetIBP.Group => Physics.LorentzJetIBP.Group,
  GUT.LorentzJetIBP.kinetic => Physics.LorentzJetIBP.kinetic,
  GUT.LorentzJetIBP.kinetic.eq_1 => Physics.LorentzJetIBP.kinetic.eq_1,
  GUT.LorentzJetIBP.kinetic_formula => Physics.LorentzJetIBP.kinetic_formula,
  GUT.LorentzJetIBP.kinetic_invariant => Physics.LorentzJetIBP.kinetic_invariant,
  GUT.LorentzJetIBP.scalarAction => Physics.LorentzJetIBP.scalarAction,
  GUT.LorentzJetIBP.scalarCoefficientEquiv => Physics.LorentzJetIBP.scalarCoefficientEquiv,
  GUT.LorentzJetIBP.scalarField => Physics.LorentzJetIBP.scalarField,
  GUT.LorentzJetIBP.spinorBasis => Physics.LorentzJetIBP.spinorBasis,
  GUT.LorentzJetIBP.waveField => Physics.LorentzJetIBP.waveField,
  GUT.LorentzJetIBP.waveField_invariant => Physics.LorentzJetIBP.waveField_invariant,
  GUT.LorentzJetIBP.weyl => Physics.LorentzJetIBP.weyl,
  GUT.LorentzJetIBP.weylMixedCoefficientEquiv => Physics.LorentzJetIBP.weylMixedCoefficientEquiv,
  GUT.LorentzJetIBP.weylSourceEquiv => Physics.LorentzJetIBP.weylSourceEquiv,
  GUT.LorentzJetIBP.weyl_basis => Physics.LorentzJetIBP.weyl_basis,
  GUT.LorentzJetIBP.weyl_derivative => Physics.LorentzJetIBP.weyl_derivative
]

assert_compatible GUT.LorentzJetIBP.Group => Physics.LorentzJetIBP.Group
assert_compatible GUT.LorentzJetIBP.kinetic => Physics.LorentzJetIBP.kinetic
assert_compatible GUT.LorentzJetIBP.kinetic.eq_1 => Physics.LorentzJetIBP.kinetic.eq_1
assert_compatible GUT.LorentzJetIBP.kinetic_formula => Physics.LorentzJetIBP.kinetic_formula
assert_compatible GUT.LorentzJetIBP.kinetic_invariant => Physics.LorentzJetIBP.kinetic_invariant
assert_compatible GUT.LorentzJetIBP.scalarAction => Physics.LorentzJetIBP.scalarAction
assert_compatible GUT.LorentzJetIBP.scalarCoefficientEquiv => Physics.LorentzJetIBP.scalarCoefficientEquiv
assert_compatible GUT.LorentzJetIBP.scalarField => Physics.LorentzJetIBP.scalarField
assert_compatible GUT.LorentzJetIBP.spinorBasis => Physics.LorentzJetIBP.spinorBasis
assert_compatible GUT.LorentzJetIBP.waveField => Physics.LorentzJetIBP.waveField
assert_compatible GUT.LorentzJetIBP.waveField_invariant => Physics.LorentzJetIBP.waveField_invariant
assert_compatible GUT.LorentzJetIBP.weyl => Physics.LorentzJetIBP.weyl
assert_compatible GUT.LorentzJetIBP.weylMixedCoefficientEquiv => Physics.LorentzJetIBP.weylMixedCoefficientEquiv
assert_compatible GUT.LorentzJetIBP.weylSourceEquiv => Physics.LorentzJetIBP.weylSourceEquiv
assert_compatible GUT.LorentzJetIBP.weyl_basis => Physics.LorentzJetIBP.weyl_basis
assert_compatible GUT.LorentzJetIBP.weyl_derivative => Physics.LorentzJetIBP.weyl_derivative
