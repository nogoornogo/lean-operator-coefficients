import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFiniteFlavor
import Physics.StandardModel.Operators.QqqlFlavorComponents
import Math.RepresentationTheory.TripleFlavorCounting
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFiniteFlavor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlFiniteFlavor.Coordinates => Physics.QqqlFiniteFlavor.Coordinates,
  GUT.QqqlFiniteFlavor.ResidualCondition => Physics.QqqlFiniteFlavor.ResidualCondition,
  GUT.QqqlFiniteFlavor.Tensor => Physics.QqqlFiniteFlavor.Tensor,
  GUT.QqqlFiniteFlavor.basisValue => Physics.QqqlFiniteFlavor.basisValue,
  GUT.QqqlFiniteFlavor.basisValue.eq_1 => Physics.QqqlFiniteFlavor.basisValue.eq_1,
  GUT.QqqlFiniteFlavor.equiv => Physics.QqqlFiniteFlavor.equiv,
  GUT.QqqlFiniteFlavor.exteriorEquiv => Physics.QqqlFiniteFlavor.exteriorEquiv,
  GUT.QqqlFiniteFlavor.extract => Physics.QqqlFiniteFlavor.extract,
  GUT.QqqlFiniteFlavor.extract_reconstruct => Physics.QqqlFiniteFlavor.extract_reconstruct,
  GUT.QqqlFiniteFlavor.extract_residual => Physics.QqqlFiniteFlavor.extract_residual,
  GUT.QqqlFiniteFlavor.flatten => Physics.QqqlFiniteFlavor.flatten,
  GUT.QqqlFiniteFlavor.flavorBasis => Physics.QqqlFiniteFlavor.flavorBasis,
  GUT.QqqlFiniteFlavor.flavorBasis_independent => Physics.QqqlFiniteFlavor.flavorBasis_independent,
  GUT.QqqlFiniteFlavor.flavorBasis_spans => Physics.QqqlFiniteFlavor.flavorBasis_spans,
  GUT.QqqlFiniteFlavor.flavorEquiv => Physics.QqqlFiniteFlavor.flavorEquiv,
  GUT.QqqlFiniteFlavor.flavor_finrank => Physics.QqqlFiniteFlavor.flavor_finrank,
  GUT.QqqlFiniteFlavor.flavor_finrank_binomial => Physics.QqqlFiniteFlavor.flavor_finrank_binomial,
  GUT.QqqlFiniteFlavor.onFieldsEquiv => Physics.QqqlFiniteFlavor.onFieldsEquiv,
  GUT.QqqlFiniteFlavor.raw => Physics.QqqlFiniteFlavor.raw,
  GUT.QqqlFiniteFlavor.raw.eq_1 => Physics.QqqlFiniteFlavor.raw.eq_1,
  GUT.QqqlFiniteFlavor.raw_add => Physics.QqqlFiniteFlavor.raw_add,
  GUT.QqqlFiniteFlavor.raw_basis => Physics.QqqlFiniteFlavor.raw_basis,
  GUT.QqqlFiniteFlavor.raw_extract => Physics.QqqlFiniteFlavor.raw_extract,
  GUT.QqqlFiniteFlavor.raw_smul => Physics.QqqlFiniteFlavor.raw_smul,
  GUT.QqqlFiniteFlavor.raw_zero => Physics.QqqlFiniteFlavor.raw_zero,
  GUT.QqqlFiniteFlavor.reconstruct => Physics.QqqlFiniteFlavor.reconstruct,
  GUT.QqqlFiniteFlavor.reconstruct_extract => Physics.QqqlFiniteFlavor.reconstruct_extract,
  GUT.QqqlFiniteFlavor.space => Physics.QqqlFiniteFlavor.space,
  GUT.QqqlFiniteFlavor.table => Physics.QqqlFiniteFlavor.table,
  GUT.QqqlFiniteFlavor.table.eq_1 => Physics.QqqlFiniteFlavor.table.eq_1,
  GUT.QqqlFiniteFlavor.tensorBasis => Physics.QqqlFiniteFlavor.tensorBasis,
  GUT.QqqlFiniteFlavor.tensorBasis.eq_1 => Physics.QqqlFiniteFlavor.tensorBasis.eq_1,
  GUT.QqqlFiniteFlavor.three_generation_finrank => Physics.QqqlFiniteFlavor.three_generation_finrank,
  GUT.QqqlFiniteFlavor.trivialSpaceEquiv => Physics.QqqlFiniteFlavor.trivialSpaceEquiv,
  GUT.QqqlFiniteFlavor.trivial_residual => Physics.QqqlFiniteFlavor.trivial_residual,
  GUT.QqqlFlavorComponents.flavorTable.eq_1 => Physics.QqqlFlavorComponents.flavorTable.eq_1,
  GUT.QqqlFlavorComponents.mixedTable.eq_1 => Physics.QqqlFlavorComponents.mixedTable.eq_1
]

assert_compatible GUT.QqqlFiniteFlavor.Coordinates => Physics.QqqlFiniteFlavor.Coordinates
assert_compatible GUT.QqqlFiniteFlavor.ResidualCondition => Physics.QqqlFiniteFlavor.ResidualCondition
assert_compatible GUT.QqqlFiniteFlavor.Tensor => Physics.QqqlFiniteFlavor.Tensor
assert_compatible GUT.QqqlFiniteFlavor.basisValue => Physics.QqqlFiniteFlavor.basisValue
assert_compatible GUT.QqqlFiniteFlavor.basisValue.eq_1 => Physics.QqqlFiniteFlavor.basisValue.eq_1
assert_compatible GUT.QqqlFiniteFlavor.equiv => Physics.QqqlFiniteFlavor.equiv
assert_compatible GUT.QqqlFiniteFlavor.exteriorEquiv => Physics.QqqlFiniteFlavor.exteriorEquiv
assert_compatible GUT.QqqlFiniteFlavor.extract => Physics.QqqlFiniteFlavor.extract
assert_compatible GUT.QqqlFiniteFlavor.extract_reconstruct => Physics.QqqlFiniteFlavor.extract_reconstruct
assert_compatible GUT.QqqlFiniteFlavor.extract_residual => Physics.QqqlFiniteFlavor.extract_residual
assert_compatible GUT.QqqlFiniteFlavor.flatten => Physics.QqqlFiniteFlavor.flatten
assert_compatible GUT.QqqlFiniteFlavor.flavorBasis => Physics.QqqlFiniteFlavor.flavorBasis
assert_compatible GUT.QqqlFiniteFlavor.flavorBasis_independent => Physics.QqqlFiniteFlavor.flavorBasis_independent
assert_compatible GUT.QqqlFiniteFlavor.flavorBasis_spans => Physics.QqqlFiniteFlavor.flavorBasis_spans
assert_compatible GUT.QqqlFiniteFlavor.flavorEquiv => Physics.QqqlFiniteFlavor.flavorEquiv
assert_compatible GUT.QqqlFiniteFlavor.flavor_finrank => Physics.QqqlFiniteFlavor.flavor_finrank
assert_compatible GUT.QqqlFiniteFlavor.flavor_finrank_binomial => Physics.QqqlFiniteFlavor.flavor_finrank_binomial
assert_compatible GUT.QqqlFiniteFlavor.onFieldsEquiv => Physics.QqqlFiniteFlavor.onFieldsEquiv
assert_compatible GUT.QqqlFiniteFlavor.raw => Physics.QqqlFiniteFlavor.raw
assert_compatible GUT.QqqlFiniteFlavor.raw.eq_1 => Physics.QqqlFiniteFlavor.raw.eq_1
assert_compatible GUT.QqqlFiniteFlavor.raw_add => Physics.QqqlFiniteFlavor.raw_add
assert_compatible GUT.QqqlFiniteFlavor.raw_basis => Physics.QqqlFiniteFlavor.raw_basis
assert_compatible GUT.QqqlFiniteFlavor.raw_extract => Physics.QqqlFiniteFlavor.raw_extract
assert_compatible GUT.QqqlFiniteFlavor.raw_smul => Physics.QqqlFiniteFlavor.raw_smul
assert_compatible GUT.QqqlFiniteFlavor.raw_zero => Physics.QqqlFiniteFlavor.raw_zero
assert_compatible GUT.QqqlFiniteFlavor.reconstruct => Physics.QqqlFiniteFlavor.reconstruct
assert_compatible GUT.QqqlFiniteFlavor.reconstruct_extract => Physics.QqqlFiniteFlavor.reconstruct_extract
assert_compatible GUT.QqqlFiniteFlavor.space => Physics.QqqlFiniteFlavor.space
assert_compatible GUT.QqqlFiniteFlavor.table => Physics.QqqlFiniteFlavor.table
assert_compatible GUT.QqqlFiniteFlavor.table.eq_1 => Physics.QqqlFiniteFlavor.table.eq_1
assert_compatible GUT.QqqlFiniteFlavor.tensorBasis => Physics.QqqlFiniteFlavor.tensorBasis
assert_compatible GUT.QqqlFiniteFlavor.tensorBasis.eq_1 => Physics.QqqlFiniteFlavor.tensorBasis.eq_1
assert_compatible GUT.QqqlFiniteFlavor.three_generation_finrank => Physics.QqqlFiniteFlavor.three_generation_finrank
assert_compatible GUT.QqqlFiniteFlavor.trivialSpaceEquiv => Physics.QqqlFiniteFlavor.trivialSpaceEquiv
assert_compatible GUT.QqqlFiniteFlavor.trivial_residual => Physics.QqqlFiniteFlavor.trivial_residual
assert_compatible GUT.QqqlFlavorComponents.flavorTable.eq_1 => Physics.QqqlFlavorComponents.flavorTable.eq_1
assert_compatible GUT.QqqlFlavorComponents.mixedTable.eq_1 => Physics.QqqlFlavorComponents.mixedTable.eq_1
