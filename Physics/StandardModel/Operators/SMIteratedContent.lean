import Physics.StandardModel.Operators.Support.Coordinates.SMIteratedContent
import Math.RepresentationTheory.IndexedExteriorContent
import Physics.StandardModel.Operators.SMChargedKernelRank
import Physics.StandardModel.Operators.SMParityKernelRank
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMIteratedContent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMIteratedContent.carrier_dimension => Physics.SMIteratedContent.carrier_dimension,
  GUT.SMIteratedContent.charged_rank => Physics.SMIteratedContent.charged_rank,
  GUT.SMIteratedContent.coefficientEquiv => Physics.SMIteratedContent.coefficientEquiv,
  GUT.SMIteratedContent.columns => Physics.SMIteratedContent.columns,
  GUT.SMIteratedContent.columns.eq_1 => Physics.SMIteratedContent.columns.eq_1,
  GUT.SMIteratedContent.counts => Physics.SMIteratedContent.counts,
  GUT.SMIteratedContent.degree_eq => Physics.SMIteratedContent.degree_eq,
  GUT.SMIteratedContent.factor => Physics.SMIteratedContent.factor,
  GUT.SMIteratedContent.fieldEquiv => Physics.SMIteratedContent.fieldEquiv,
  GUT.SMIteratedContent.fieldFinite => Physics.SMIteratedContent.fieldFinite,
  GUT.SMIteratedContent.labelEquiv => Physics.SMIteratedContent.labelEquiv,
  GUT.SMIteratedContent.leaves => Physics.SMIteratedContent.leaves,
  GUT.SMIteratedContent.odd_rank => Physics.SMIteratedContent.odd_rank,
  GUT.SMIteratedContent.rank_add_nullity => Physics.SMIteratedContent.rank_add_nullity,
  GUT.SMIteratedContent.sourceDimension => Physics.SMIteratedContent.sourceDimension,
  GUT.SMIteratedContent.sourceEquiv => Physics.SMIteratedContent.sourceEquiv,
  GUT.SMIteratedContent.source_character => Physics.SMIteratedContent.source_character,
  GUT.SMIteratedContent.source_dimension => Physics.SMIteratedContent.source_dimension,
  GUT.SMIteratedContent.tree => Physics.SMIteratedContent.tree,
  GUT.SMIteratedContent.withSpectator => Physics.SMIteratedContent.withSpectator
]

assert_compatible GUT.SMIteratedContent.carrier_dimension => Physics.SMIteratedContent.carrier_dimension
assert_compatible GUT.SMIteratedContent.charged_rank => Physics.SMIteratedContent.charged_rank
assert_compatible GUT.SMIteratedContent.coefficientEquiv => Physics.SMIteratedContent.coefficientEquiv
assert_compatible GUT.SMIteratedContent.columns => Physics.SMIteratedContent.columns
assert_compatible GUT.SMIteratedContent.columns.eq_1 => Physics.SMIteratedContent.columns.eq_1
assert_compatible GUT.SMIteratedContent.counts => Physics.SMIteratedContent.counts
assert_compatible GUT.SMIteratedContent.degree_eq => Physics.SMIteratedContent.degree_eq
assert_compatible GUT.SMIteratedContent.factor => Physics.SMIteratedContent.factor
assert_compatible GUT.SMIteratedContent.fieldEquiv => Physics.SMIteratedContent.fieldEquiv
assert_compatible GUT.SMIteratedContent.fieldFinite => Physics.SMIteratedContent.fieldFinite
assert_compatible GUT.SMIteratedContent.labelEquiv => Physics.SMIteratedContent.labelEquiv
assert_compatible GUT.SMIteratedContent.leaves => Physics.SMIteratedContent.leaves
assert_compatible GUT.SMIteratedContent.odd_rank => Physics.SMIteratedContent.odd_rank
assert_compatible GUT.SMIteratedContent.rank_add_nullity => Physics.SMIteratedContent.rank_add_nullity
assert_compatible GUT.SMIteratedContent.sourceDimension => Physics.SMIteratedContent.sourceDimension
assert_compatible GUT.SMIteratedContent.sourceEquiv => Physics.SMIteratedContent.sourceEquiv
assert_compatible GUT.SMIteratedContent.source_character => Physics.SMIteratedContent.source_character
assert_compatible GUT.SMIteratedContent.source_dimension => Physics.SMIteratedContent.source_dimension
assert_compatible GUT.SMIteratedContent.tree => Physics.SMIteratedContent.tree
assert_compatible GUT.SMIteratedContent.withSpectator => Physics.SMIteratedContent.withSpectator
