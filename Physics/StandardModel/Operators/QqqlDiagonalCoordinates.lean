import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlDiagonalCoordinates
import Math.RepresentationTheory.TripleFlavorWeights
import Math.RepresentationTheory.CyclicWeightCoordinates
import Physics.StandardModel.Operators.QqqlFiniteFlavor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlDiagonalCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlDiagonalCoordinates.allowed_iff => Physics.QqqlDiagonalCoordinates.allowed_iff,
  GUT.QqqlDiagonalCoordinates.basisValue_injective => Physics.QqqlDiagonalCoordinates.basisValue_injective,
  GUT.QqqlDiagonalCoordinates.basisValue_scale => Physics.QqqlDiagonalCoordinates.basisValue_scale,
  GUT.QqqlDiagonalCoordinates.charge => Physics.QqqlDiagonalCoordinates.charge,
  GUT.QqqlDiagonalCoordinates.charge.eq_1 => Physics.QqqlDiagonalCoordinates.charge.eq_1,
  GUT.QqqlDiagonalCoordinates.diagonalEquiv => Physics.QqqlDiagonalCoordinates.diagonalEquiv,
  GUT.QqqlDiagonalCoordinates.diagonal_allowed_iff => Physics.QqqlDiagonalCoordinates.diagonal_allowed_iff,
  GUT.QqqlDiagonalCoordinates.diagonal_forbidden_iff => Physics.QqqlDiagonalCoordinates.diagonal_forbidden_iff,
  GUT.QqqlDiagonalCoordinates.equiv => Physics.QqqlDiagonalCoordinates.equiv,
  GUT.QqqlDiagonalCoordinates.finiteBasis => Physics.QqqlDiagonalCoordinates.finiteBasis,
  GUT.QqqlDiagonalCoordinates.finiteBasis.eq_1 => Physics.QqqlDiagonalCoordinates.finiteBasis.eq_1,
  GUT.QqqlDiagonalCoordinates.finite_weights => Physics.QqqlDiagonalCoordinates.finite_weights,
  GUT.QqqlDiagonalCoordinates.finrank => Physics.QqqlDiagonalCoordinates.finrank,
  GUT.QqqlDiagonalCoordinates.raw_scale => Physics.QqqlDiagonalCoordinates.raw_scale,
  GUT.QqqlDiagonalCoordinates.residual_iff_scale => Physics.QqqlDiagonalCoordinates.residual_iff_scale,
  GUT.QqqlDiagonalCoordinates.residual_iff_supported => Physics.QqqlDiagonalCoordinates.residual_iff_supported,
  GUT.QqqlDiagonalCoordinates.scale => Physics.QqqlDiagonalCoordinates.scale,
  GUT.QqqlDiagonalCoordinates.scale.eq_1 => Physics.QqqlDiagonalCoordinates.scale.eq_1,
  GUT.QqqlDiagonalCoordinates.scale_character => Physics.QqqlDiagonalCoordinates.scale_character,
  GUT.QqqlDiagonalCoordinates.spaceEquiv => Physics.QqqlDiagonalCoordinates.spaceEquiv
]

assert_compatible GUT.QqqlDiagonalCoordinates.allowed_iff => Physics.QqqlDiagonalCoordinates.allowed_iff
assert_compatible GUT.QqqlDiagonalCoordinates.basisValue_injective => Physics.QqqlDiagonalCoordinates.basisValue_injective
assert_compatible GUT.QqqlDiagonalCoordinates.basisValue_scale => Physics.QqqlDiagonalCoordinates.basisValue_scale
assert_compatible GUT.QqqlDiagonalCoordinates.charge => Physics.QqqlDiagonalCoordinates.charge
assert_compatible GUT.QqqlDiagonalCoordinates.charge.eq_1 => Physics.QqqlDiagonalCoordinates.charge.eq_1
assert_compatible GUT.QqqlDiagonalCoordinates.diagonalEquiv => Physics.QqqlDiagonalCoordinates.diagonalEquiv
assert_compatible GUT.QqqlDiagonalCoordinates.diagonal_allowed_iff => Physics.QqqlDiagonalCoordinates.diagonal_allowed_iff
assert_compatible GUT.QqqlDiagonalCoordinates.diagonal_forbidden_iff => Physics.QqqlDiagonalCoordinates.diagonal_forbidden_iff
assert_compatible GUT.QqqlDiagonalCoordinates.equiv => Physics.QqqlDiagonalCoordinates.equiv
assert_compatible GUT.QqqlDiagonalCoordinates.finiteBasis => Physics.QqqlDiagonalCoordinates.finiteBasis
assert_compatible GUT.QqqlDiagonalCoordinates.finiteBasis.eq_1 => Physics.QqqlDiagonalCoordinates.finiteBasis.eq_1
assert_compatible GUT.QqqlDiagonalCoordinates.finite_weights => Physics.QqqlDiagonalCoordinates.finite_weights
assert_compatible GUT.QqqlDiagonalCoordinates.finrank => Physics.QqqlDiagonalCoordinates.finrank
assert_compatible GUT.QqqlDiagonalCoordinates.raw_scale => Physics.QqqlDiagonalCoordinates.raw_scale
assert_compatible GUT.QqqlDiagonalCoordinates.residual_iff_scale => Physics.QqqlDiagonalCoordinates.residual_iff_scale
assert_compatible GUT.QqqlDiagonalCoordinates.residual_iff_supported => Physics.QqqlDiagonalCoordinates.residual_iff_supported
assert_compatible GUT.QqqlDiagonalCoordinates.scale => Physics.QqqlDiagonalCoordinates.scale
assert_compatible GUT.QqqlDiagonalCoordinates.scale.eq_1 => Physics.QqqlDiagonalCoordinates.scale.eq_1
assert_compatible GUT.QqqlDiagonalCoordinates.scale_character => Physics.QqqlDiagonalCoordinates.scale_character
assert_compatible GUT.QqqlDiagonalCoordinates.spaceEquiv => Physics.QqqlDiagonalCoordinates.spaceEquiv
