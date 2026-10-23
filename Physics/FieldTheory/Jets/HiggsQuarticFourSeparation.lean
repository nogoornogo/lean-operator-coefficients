import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourSeparation
import Physics.FieldTheory.Jets.HiggsQuarticFourWaves
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourSeparation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourSeparation.CandidateImage => Physics.HiggsQuarticFourSeparation.CandidateImage,
  GUT.HiggsQuarticFourSeparation.amplitudes => Physics.HiggsQuarticFourSeparation.amplitudes,
  GUT.HiggsQuarticFourSeparation.amplitudes.eq_1 => Physics.HiggsQuarticFourSeparation.amplitudes.eq_1,
  GUT.HiggsQuarticFourSeparation.annihilates => Physics.HiggsQuarticFourSeparation.annihilates,
  GUT.HiggsQuarticFourSeparation.candidateEquivalence => Physics.HiggsQuarticFourSeparation.candidateEquivalence,
  GUT.HiggsQuarticFourSeparation.candidate_dimension => Physics.HiggsQuarticFourSeparation.candidate_dimension,
  GUT.HiggsQuarticFourSeparation.combination => Physics.HiggsQuarticFourSeparation.combination,
  GUT.HiggsQuarticFourSeparation.combination_injective => Physics.HiggsQuarticFourSeparation.combination_injective,
  GUT.HiggsQuarticFourSeparation.conservation => Physics.HiggsQuarticFourSeparation.conservation,
  GUT.HiggsQuarticFourSeparation.coordinates => Physics.HiggsQuarticFourSeparation.coordinates,
  GUT.HiggsQuarticFourSeparation.coordinates_combination => Physics.HiggsQuarticFourSeparation.coordinates_combination,
  GUT.HiggsQuarticFourSeparation.decoder => Physics.HiggsQuarticFourSeparation.decoder,
  GUT.HiggsQuarticFourSeparation.decoder_value => Physics.HiggsQuarticFourSeparation.decoder_value,
  GUT.HiggsQuarticFourSeparation.evaluation_first => Physics.HiggsQuarticFourSeparation.evaluation_first,
  GUT.HiggsQuarticFourSeparation.independent_mod_relations => Physics.HiggsQuarticFourSeparation.independent_mod_relations,
  GUT.HiggsQuarticFourSeparation.inverseMatrix => Physics.HiggsQuarticFourSeparation.inverseMatrix,
  GUT.HiggsQuarticFourSeparation.inverseMatrix.eq_1 => Physics.HiggsQuarticFourSeparation.inverseMatrix.eq_1,
  GUT.HiggsQuarticFourSeparation.momenta => Physics.HiggsQuarticFourSeparation.momenta,
  GUT.HiggsQuarticFourSeparation.momenta.eq_1 => Physics.HiggsQuarticFourSeparation.momenta.eq_1,
  GUT.HiggsQuarticFourSeparation.null => Physics.HiggsQuarticFourSeparation.null,
  GUT.HiggsQuarticFourSeparation.q1_value => Physics.HiggsQuarticFourSeparation.q1_value,
  GUT.HiggsQuarticFourSeparation.q2_value => Physics.HiggsQuarticFourSeparation.q2_value,
  GUT.HiggsQuarticFourSeparation.q3_value => Physics.HiggsQuarticFourSeparation.q3_value,
  GUT.HiggsQuarticFourSeparation.quotient => Physics.HiggsQuarticFourSeparation.quotient,
  GUT.HiggsQuarticFourSeparation.quotient_projection => Physics.HiggsQuarticFourSeparation.quotient_projection,
  GUT.HiggsQuarticFourSeparation.representative_value => Physics.HiggsQuarticFourSeparation.representative_value,
  GUT.HiggsQuarticFourSeparation.separator => Physics.HiggsQuarticFourSeparation.separator,
  GUT.HiggsQuarticFourSeparation.slot => Physics.HiggsQuarticFourSeparation.slot,
  GUT.HiggsQuarticFourSeparation.slot.eq_1 => Physics.HiggsQuarticFourSeparation.slot.eq_1,
  GUT.HiggsQuarticFourSeparation.values => Physics.HiggsQuarticFourSeparation.values,
  GUT.HiggsQuarticFourSeparation.values.eq_1 => Physics.HiggsQuarticFourSeparation.values.eq_1
]

assert_compatible GUT.HiggsQuarticFourSeparation.CandidateImage => Physics.HiggsQuarticFourSeparation.CandidateImage
assert_compatible GUT.HiggsQuarticFourSeparation.amplitudes => Physics.HiggsQuarticFourSeparation.amplitudes
assert_compatible GUT.HiggsQuarticFourSeparation.amplitudes.eq_1 => Physics.HiggsQuarticFourSeparation.amplitudes.eq_1
assert_compatible GUT.HiggsQuarticFourSeparation.annihilates => Physics.HiggsQuarticFourSeparation.annihilates
assert_compatible GUT.HiggsQuarticFourSeparation.candidateEquivalence => Physics.HiggsQuarticFourSeparation.candidateEquivalence
assert_compatible GUT.HiggsQuarticFourSeparation.candidate_dimension => Physics.HiggsQuarticFourSeparation.candidate_dimension
assert_compatible GUT.HiggsQuarticFourSeparation.combination => Physics.HiggsQuarticFourSeparation.combination
assert_compatible GUT.HiggsQuarticFourSeparation.combination_injective => Physics.HiggsQuarticFourSeparation.combination_injective
assert_compatible GUT.HiggsQuarticFourSeparation.conservation => Physics.HiggsQuarticFourSeparation.conservation
assert_compatible GUT.HiggsQuarticFourSeparation.coordinates => Physics.HiggsQuarticFourSeparation.coordinates
assert_compatible GUT.HiggsQuarticFourSeparation.coordinates_combination => Physics.HiggsQuarticFourSeparation.coordinates_combination
assert_compatible GUT.HiggsQuarticFourSeparation.decoder => Physics.HiggsQuarticFourSeparation.decoder
assert_compatible GUT.HiggsQuarticFourSeparation.decoder_value => Physics.HiggsQuarticFourSeparation.decoder_value
assert_compatible GUT.HiggsQuarticFourSeparation.evaluation_first => Physics.HiggsQuarticFourSeparation.evaluation_first
assert_compatible GUT.HiggsQuarticFourSeparation.independent_mod_relations => Physics.HiggsQuarticFourSeparation.independent_mod_relations
assert_compatible GUT.HiggsQuarticFourSeparation.inverseMatrix => Physics.HiggsQuarticFourSeparation.inverseMatrix
assert_compatible GUT.HiggsQuarticFourSeparation.inverseMatrix.eq_1 => Physics.HiggsQuarticFourSeparation.inverseMatrix.eq_1
assert_compatible GUT.HiggsQuarticFourSeparation.momenta => Physics.HiggsQuarticFourSeparation.momenta
assert_compatible GUT.HiggsQuarticFourSeparation.momenta.eq_1 => Physics.HiggsQuarticFourSeparation.momenta.eq_1
assert_compatible GUT.HiggsQuarticFourSeparation.null => Physics.HiggsQuarticFourSeparation.null
assert_compatible GUT.HiggsQuarticFourSeparation.q1_value => Physics.HiggsQuarticFourSeparation.q1_value
assert_compatible GUT.HiggsQuarticFourSeparation.q2_value => Physics.HiggsQuarticFourSeparation.q2_value
assert_compatible GUT.HiggsQuarticFourSeparation.q3_value => Physics.HiggsQuarticFourSeparation.q3_value
assert_compatible GUT.HiggsQuarticFourSeparation.quotient => Physics.HiggsQuarticFourSeparation.quotient
assert_compatible GUT.HiggsQuarticFourSeparation.quotient_projection => Physics.HiggsQuarticFourSeparation.quotient_projection
assert_compatible GUT.HiggsQuarticFourSeparation.representative_value => Physics.HiggsQuarticFourSeparation.representative_value
assert_compatible GUT.HiggsQuarticFourSeparation.separator => Physics.HiggsQuarticFourSeparation.separator
assert_compatible GUT.HiggsQuarticFourSeparation.slot => Physics.HiggsQuarticFourSeparation.slot
assert_compatible GUT.HiggsQuarticFourSeparation.slot.eq_1 => Physics.HiggsQuarticFourSeparation.slot.eq_1
assert_compatible GUT.HiggsQuarticFourSeparation.values => Physics.HiggsQuarticFourSeparation.values
assert_compatible GUT.HiggsQuarticFourSeparation.values.eq_1 => Physics.HiggsQuarticFourSeparation.values.eq_1
