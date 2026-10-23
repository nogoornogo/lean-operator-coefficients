import Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM
import Math.RepresentationTheory.NonlinearJetIBP
import Physics.FieldTheory.Jets.MasslessScalarEOM
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PolynomialScalarEOM.D => Physics.PolynomialScalarEOM.D,
  GUT.PolynomialScalarEOM.OffShell => Physics.PolynomialScalarEOM.OffShell,
  GUT.PolynomialScalarEOM.Shell => Physics.PolynomialScalarEOM.Shell,
  GUT.PolynomialScalarEOM.coefficientEquiv => Physics.PolynomialScalarEOM.coefficientEquiv,
  GUT.PolynomialScalarEOM.derivative_covariance => Physics.PolynomialScalarEOM.derivative_covariance,
  GUT.PolynomialScalarEOM.descendants_zero => Physics.PolynomialScalarEOM.descendants_zero,
  GUT.PolynomialScalarEOM.equations => Physics.PolynomialScalarEOM.equations,
  GUT.PolynomialScalarEOM.field => Physics.PolynomialScalarEOM.field,
  GUT.PolynomialScalarEOM.field_invariant => Physics.PolynomialScalarEOM.field_invariant,
  GUT.PolynomialScalarEOM.finiteImage => Physics.PolynomialScalarEOM.finiteImage,
  GUT.PolynomialScalarEOM.finiteImage_finite => Physics.PolynomialScalarEOM.finiteImage_finite,
  GUT.PolynomialScalarEOM.ideal => Physics.PolynomialScalarEOM.ideal,
  GUT.PolynomialScalarEOM.ideal_invariant => Physics.PolynomialScalarEOM.ideal_invariant,
  GUT.PolynomialScalarEOM.integrated => Physics.PolynomialScalarEOM.integrated,
  GUT.PolynomialScalarEOM.kinetic_mod_ibp => Physics.PolynomialScalarEOM.kinetic_mod_ibp,
  GUT.PolynomialScalarEOM.kinetic_relation => Physics.PolynomialScalarEOM.kinetic_relation,
  GUT.PolynomialScalarEOM.lorentzIBPTransport => Physics.PolynomialScalarEOM.lorentzIBPTransport,
  GUT.PolynomialScalarEOM.lorentzTransport => Physics.PolynomialScalarEOM.lorentzTransport,
  GUT.PolynomialScalarEOM.offAction => Physics.PolynomialScalarEOM.offAction,
  GUT.PolynomialScalarEOM.offAction.eq_1 => Physics.PolynomialScalarEOM.offAction.eq_1,
  GUT.PolynomialScalarEOM.projection => Physics.PolynomialScalarEOM.projection,
  GUT.PolynomialScalarEOM.seed => Physics.PolynomialScalarEOM.seed,
  GUT.PolynomialScalarEOM.seed.eq_1 => Physics.PolynomialScalarEOM.seed.eq_1,
  GUT.PolynomialScalarEOM.seed_invariant => Physics.PolynomialScalarEOM.seed_invariant,
  GUT.PolynomialScalarEOM.seed_zero => Physics.PolynomialScalarEOM.seed_zero,
  GUT.PolynomialScalarEOM.sourceEquiv => Physics.PolynomialScalarEOM.sourceEquiv,
  GUT.PolynomialScalarEOM.unit_survives => Physics.PolynomialScalarEOM.unit_survives,
  GUT.PolynomialScalarEOM.zeroEvaluation_seed => Physics.PolynomialScalarEOM.zeroEvaluation_seed
]

assert_compatible GUT.PolynomialScalarEOM.D => Physics.PolynomialScalarEOM.D
assert_compatible GUT.PolynomialScalarEOM.OffShell => Physics.PolynomialScalarEOM.OffShell
assert_compatible GUT.PolynomialScalarEOM.Shell => Physics.PolynomialScalarEOM.Shell
assert_compatible GUT.PolynomialScalarEOM.coefficientEquiv => Physics.PolynomialScalarEOM.coefficientEquiv
assert_compatible GUT.PolynomialScalarEOM.derivative_covariance => Physics.PolynomialScalarEOM.derivative_covariance
assert_compatible GUT.PolynomialScalarEOM.descendants_zero => Physics.PolynomialScalarEOM.descendants_zero
assert_compatible GUT.PolynomialScalarEOM.equations => Physics.PolynomialScalarEOM.equations
assert_compatible GUT.PolynomialScalarEOM.field => Physics.PolynomialScalarEOM.field
assert_compatible GUT.PolynomialScalarEOM.field_invariant => Physics.PolynomialScalarEOM.field_invariant
assert_compatible GUT.PolynomialScalarEOM.finiteImage => Physics.PolynomialScalarEOM.finiteImage
assert_compatible GUT.PolynomialScalarEOM.finiteImage_finite => Physics.PolynomialScalarEOM.finiteImage_finite
assert_compatible GUT.PolynomialScalarEOM.ideal => Physics.PolynomialScalarEOM.ideal
assert_compatible GUT.PolynomialScalarEOM.ideal_invariant => Physics.PolynomialScalarEOM.ideal_invariant
assert_compatible GUT.PolynomialScalarEOM.integrated => Physics.PolynomialScalarEOM.integrated
assert_compatible GUT.PolynomialScalarEOM.kinetic_mod_ibp => Physics.PolynomialScalarEOM.kinetic_mod_ibp
assert_compatible GUT.PolynomialScalarEOM.kinetic_relation => Physics.PolynomialScalarEOM.kinetic_relation
assert_compatible GUT.PolynomialScalarEOM.lorentzIBPTransport => Physics.PolynomialScalarEOM.lorentzIBPTransport
assert_compatible GUT.PolynomialScalarEOM.lorentzTransport => Physics.PolynomialScalarEOM.lorentzTransport
assert_compatible GUT.PolynomialScalarEOM.offAction => Physics.PolynomialScalarEOM.offAction
assert_compatible GUT.PolynomialScalarEOM.offAction.eq_1 => Physics.PolynomialScalarEOM.offAction.eq_1
assert_compatible GUT.PolynomialScalarEOM.projection => Physics.PolynomialScalarEOM.projection
assert_compatible GUT.PolynomialScalarEOM.seed => Physics.PolynomialScalarEOM.seed
assert_compatible GUT.PolynomialScalarEOM.seed.eq_1 => Physics.PolynomialScalarEOM.seed.eq_1
assert_compatible GUT.PolynomialScalarEOM.seed_invariant => Physics.PolynomialScalarEOM.seed_invariant
assert_compatible GUT.PolynomialScalarEOM.seed_zero => Physics.PolynomialScalarEOM.seed_zero
assert_compatible GUT.PolynomialScalarEOM.sourceEquiv => Physics.PolynomialScalarEOM.sourceEquiv
assert_compatible GUT.PolynomialScalarEOM.unit_survives => Physics.PolynomialScalarEOM.unit_survives
assert_compatible GUT.PolynomialScalarEOM.zeroEvaluation_seed => Physics.PolynomialScalarEOM.zeroEvaluation_seed
