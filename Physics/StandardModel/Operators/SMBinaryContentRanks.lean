import Physics.StandardModel.Operators.Support.Coordinates.SMBinaryContentRanks
import Math.RepresentationTheory.BinaryPatternExterior
import Math.RepresentationTheory.PatternMultiplicityEquiv
import Physics.StandardModel.Operators.SMConstantContentRanks
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMBinaryContentRanks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMBinaryContentRanks.carrier_dimension => Physics.SMBinaryContentRanks.carrier_dimension,
  GUT.SMBinaryContentRanks.charge => Physics.SMBinaryContentRanks.charge,
  GUT.SMBinaryContentRanks.charged_rank => Physics.SMBinaryContentRanks.charged_rank,
  GUT.SMBinaryContentRanks.columns => Physics.SMBinaryContentRanks.columns,
  GUT.SMBinaryContentRanks.columns.eq_1 => Physics.SMBinaryContentRanks.columns.eq_1,
  GUT.SMBinaryContentRanks.fieldFinite => Physics.SMBinaryContentRanks.fieldFinite,
  GUT.SMBinaryContentRanks.odd_rank => Physics.SMBinaryContentRanks.odd_rank,
  GUT.SMBinaryContentRanks.pattern => Physics.SMBinaryContentRanks.pattern,
  GUT.SMBinaryContentRanks.rank_add_nullity => Physics.SMBinaryContentRanks.rank_add_nullity,
  GUT.SMBinaryContentRanks.reordered_source_dimension => Physics.SMBinaryContentRanks.reordered_source_dimension,
  GUT.SMBinaryContentRanks.sourceEquiv => Physics.SMBinaryContentRanks.sourceEquiv,
  GUT.SMBinaryContentRanks.source_dimension => Physics.SMBinaryContentRanks.source_dimension
]

assert_compatible GUT.SMBinaryContentRanks.carrier_dimension => Physics.SMBinaryContentRanks.carrier_dimension
assert_compatible GUT.SMBinaryContentRanks.charge => Physics.SMBinaryContentRanks.charge
assert_compatible GUT.SMBinaryContentRanks.charged_rank => Physics.SMBinaryContentRanks.charged_rank
assert_compatible GUT.SMBinaryContentRanks.columns => Physics.SMBinaryContentRanks.columns
assert_compatible GUT.SMBinaryContentRanks.columns.eq_1 => Physics.SMBinaryContentRanks.columns.eq_1
assert_compatible GUT.SMBinaryContentRanks.fieldFinite => Physics.SMBinaryContentRanks.fieldFinite
assert_compatible GUT.SMBinaryContentRanks.odd_rank => Physics.SMBinaryContentRanks.odd_rank
assert_compatible GUT.SMBinaryContentRanks.pattern => Physics.SMBinaryContentRanks.pattern
assert_compatible GUT.SMBinaryContentRanks.rank_add_nullity => Physics.SMBinaryContentRanks.rank_add_nullity
assert_compatible GUT.SMBinaryContentRanks.reordered_source_dimension => Physics.SMBinaryContentRanks.reordered_source_dimension
assert_compatible GUT.SMBinaryContentRanks.sourceEquiv => Physics.SMBinaryContentRanks.sourceEquiv
assert_compatible GUT.SMBinaryContentRanks.source_dimension => Physics.SMBinaryContentRanks.source_dimension
