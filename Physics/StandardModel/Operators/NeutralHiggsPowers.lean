import Physics.StandardModel.Operators.Higgs.NeutralHiggsPowers
import Physics.StandardModel.Operators.BnvMixedInput
import Physics.FieldTheory.Mass.LightInheritanceBoundary
import Physics.FieldTheory.Mass.EquivariantWeylMassTransport
import Math.RepresentationTheory.MixedInvariantDressing
import Math.RepresentationTheory.ExternalUnitEquivalence
import Physics.StandardModel.Operators.BnvSevenModelInterface
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.NeutralHiggsPowers instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DiracWeylConvention.massBilinear.eq_1 => Physics.DiracWeylConvention.massBilinear.eq_1,
  GUT.NeutralHiggsPowers.Fields => Physics.NeutralHiggsPowers.Fields,
  GUT.NeutralHiggsPowers.G => Physics.NeutralHiggsPowers.G,
  GUT.NeutralHiggsPowers.Multiplicity => Physics.NeutralHiggsPowers.Multiplicity,
  GUT.NeutralHiggsPowers.action => Physics.NeutralHiggsPowers.action,
  GUT.NeutralHiggsPowers.coefficient => Physics.NeutralHiggsPowers.coefficient,
  GUT.NeutralHiggsPowers.coefficient_nonzero => Physics.NeutralHiggsPowers.coefficient_nonzero,
  GUT.NeutralHiggsPowers.coordinates => Physics.NeutralHiggsPowers.coordinates,
  GUT.NeutralHiggsPowers.flavor => Physics.NeutralHiggsPowers.flavor,
  GUT.NeutralHiggsPowers.higgs => Physics.NeutralHiggsPowers.higgs,
  GUT.NeutralHiggsPowers.instAddCommGroupFields => Physics.NeutralHiggsPowers.instAddCommGroupFields,
  GUT.NeutralHiggsPowers.normalization => Physics.NeutralHiggsPowers.normalization,
  GUT.NeutralHiggsPowers.normalization_nonzero => Physics.NeutralHiggsPowers.normalization_nonzero,
  GUT.NeutralHiggsPowers.normalized => Physics.NeutralHiggsPowers.normalized,
  GUT.NeutralHiggsPowers.normalized_diagonal => Physics.NeutralHiggsPowers.normalized_diagonal,
  GUT.NeutralHiggsPowers.normalized_nonzero => Physics.NeutralHiggsPowers.normalized_nonzero,
  GUT.NeutralHiggsPowers.pairing => Physics.NeutralHiggsPowers.pairing,
  GUT.NeutralHiggsPowers.pairing.eq_1 => Physics.NeutralHiggsPowers.pairing.eq_1,
  GUT.NeutralHiggsPowers.pairing_diagonal => Physics.NeutralHiggsPowers.pairing_diagonal,
  GUT.NeutralHiggsPowers.pairing_polynomial => Physics.NeutralHiggsPowers.pairing_polynomial,
  GUT.NeutralHiggsPowers.vector => Physics.NeutralHiggsPowers.vector,
  GUT.NeutralHiggsPowers.vector.eq_1 => Physics.NeutralHiggsPowers.vector.eq_1
]

assert_compatible GUT.DiracWeylConvention.massBilinear.eq_1 => Physics.DiracWeylConvention.massBilinear.eq_1
assert_compatible GUT.NeutralHiggsPowers.Fields => Physics.NeutralHiggsPowers.Fields
assert_compatible GUT.NeutralHiggsPowers.G => Physics.NeutralHiggsPowers.G
assert_compatible GUT.NeutralHiggsPowers.Multiplicity => Physics.NeutralHiggsPowers.Multiplicity
assert_compatible GUT.NeutralHiggsPowers.action => Physics.NeutralHiggsPowers.action
assert_compatible GUT.NeutralHiggsPowers.coefficient => Physics.NeutralHiggsPowers.coefficient
assert_compatible GUT.NeutralHiggsPowers.coefficient_nonzero => Physics.NeutralHiggsPowers.coefficient_nonzero
assert_compatible GUT.NeutralHiggsPowers.coordinates => Physics.NeutralHiggsPowers.coordinates
assert_compatible GUT.NeutralHiggsPowers.flavor => Physics.NeutralHiggsPowers.flavor
assert_compatible GUT.NeutralHiggsPowers.higgs => Physics.NeutralHiggsPowers.higgs
assert_compatible GUT.NeutralHiggsPowers.instAddCommGroupFields => Physics.NeutralHiggsPowers.instAddCommGroupFields
assert_compatible GUT.NeutralHiggsPowers.normalization => Physics.NeutralHiggsPowers.normalization
assert_compatible GUT.NeutralHiggsPowers.normalization_nonzero => Physics.NeutralHiggsPowers.normalization_nonzero
assert_compatible GUT.NeutralHiggsPowers.normalized => Physics.NeutralHiggsPowers.normalized
assert_compatible GUT.NeutralHiggsPowers.normalized_diagonal => Physics.NeutralHiggsPowers.normalized_diagonal
assert_compatible GUT.NeutralHiggsPowers.normalized_nonzero => Physics.NeutralHiggsPowers.normalized_nonzero
assert_compatible GUT.NeutralHiggsPowers.pairing => Physics.NeutralHiggsPowers.pairing
assert_compatible GUT.NeutralHiggsPowers.pairing.eq_1 => Physics.NeutralHiggsPowers.pairing.eq_1
assert_compatible GUT.NeutralHiggsPowers.pairing_diagonal => Physics.NeutralHiggsPowers.pairing_diagonal
assert_compatible GUT.NeutralHiggsPowers.pairing_polynomial => Physics.NeutralHiggsPowers.pairing_polynomial
assert_compatible GUT.NeutralHiggsPowers.vector => Physics.NeutralHiggsPowers.vector
assert_compatible GUT.NeutralHiggsPowers.vector.eq_1 => Physics.NeutralHiggsPowers.vector.eq_1
