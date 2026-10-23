import Physics.StandardModel.Operators.Support.Lepton.SMLocalCoefficientGluing
import Math.RepresentationTheory.InvariantCoefficientGluing
import Math.RepresentationTheory.TwistedSU2ConstituentCoupling
import Math.RepresentationTheory.BinaryPatternExterior
import Math.RepresentationTheory.ConstantPatternExterior
import Physics.StandardModel.Operators.SMIntegralLocalWeights
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLocalCoefficientGluing instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMLocalCoefficientGluing.allowed => Physics.SMLocalCoefficientGluing.allowed,
  GUT.SMLocalCoefficientGluing.allowed_at => Physics.SMLocalCoefficientGluing.allowed_at,
  GUT.SMLocalCoefficientGluing.boson => Physics.SMLocalCoefficientGluing.boson,
  GUT.SMLocalCoefficientGluing.bosonDualIrreducible => Physics.SMLocalCoefficientGluing.bosonDualIrreducible,
  GUT.SMLocalCoefficientGluing.bosonEquiv => Physics.SMLocalCoefficientGluing.bosonEquiv,
  GUT.SMLocalCoefficientGluing.bosonIrreducible => Physics.SMLocalCoefficientGluing.bosonIrreducible,
  GUT.SMLocalCoefficientGluing.character => Physics.SMLocalCoefficientGluing.character,
  GUT.SMLocalCoefficientGluing.fullSourceEquiv => Physics.SMLocalCoefficientGluing.fullSourceEquiv,
  GUT.SMLocalCoefficientGluing.instAddCommGroupTensorProductComplex_physics => Physics.SMLocalCoefficientGluing.instAddCommGroupTensorProductComplex_physics,
  GUT.SMLocalCoefficientGluing.sourceEquiv => Physics.SMLocalCoefficientGluing.sourceEquiv,
  GUT.SMLocalCoefficientGluing.weakProjection => Physics.SMLocalCoefficientGluing.weakProjection
]

assert_compatible GUT.SMLocalCoefficientGluing.allowed => Physics.SMLocalCoefficientGluing.allowed
assert_compatible GUT.SMLocalCoefficientGluing.allowed_at => Physics.SMLocalCoefficientGluing.allowed_at
assert_compatible GUT.SMLocalCoefficientGluing.boson => Physics.SMLocalCoefficientGluing.boson
assert_compatible GUT.SMLocalCoefficientGluing.bosonDualIrreducible => Physics.SMLocalCoefficientGluing.bosonDualIrreducible
assert_compatible GUT.SMLocalCoefficientGluing.bosonEquiv => Physics.SMLocalCoefficientGluing.bosonEquiv
assert_compatible GUT.SMLocalCoefficientGluing.bosonIrreducible => Physics.SMLocalCoefficientGluing.bosonIrreducible
assert_compatible GUT.SMLocalCoefficientGluing.character => Physics.SMLocalCoefficientGluing.character
assert_compatible GUT.SMLocalCoefficientGluing.fullSourceEquiv => Physics.SMLocalCoefficientGluing.fullSourceEquiv
assert_compatible GUT.SMLocalCoefficientGluing.instAddCommGroupTensorProductComplex_physics => Physics.SMLocalCoefficientGluing.instAddCommGroupTensorProductComplex_physics
assert_compatible GUT.SMLocalCoefficientGluing.sourceEquiv => Physics.SMLocalCoefficientGluing.sourceEquiv
assert_compatible GUT.SMLocalCoefficientGluing.weakProjection => Physics.SMLocalCoefficientGluing.weakProjection
