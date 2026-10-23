import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentBasis
import Physics.FieldTheory.Jets.HiggsQuarticFourFields
import Physics.FieldTheory.Jets.HiggsQuarticFourWaves
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourMomentBasis instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourMomentBasis.annihilates => Physics.HiggsQuarticFourMomentBasis.annihilates,
  GUT.HiggsQuarticFourMomentBasis.conservation => Physics.HiggsQuarticFourMomentBasis.conservation,
  GUT.HiggsQuarticFourMomentBasis.count => Physics.HiggsQuarticFourMomentBasis.count,
  GUT.HiggsQuarticFourMomentBasis.fieldModel => Physics.HiggsQuarticFourMomentBasis.fieldModel,
  GUT.HiggsQuarticFourMomentBasis.fieldModel.eq_1 => Physics.HiggsQuarticFourMomentBasis.fieldModel.eq_1,
  GUT.HiggsQuarticFourMomentBasis.fieldModel_invariant => Physics.HiggsQuarticFourMomentBasis.fieldModel_invariant,
  GUT.HiggsQuarticFourMomentBasis.fieldTensor_eq => Physics.HiggsQuarticFourMomentBasis.fieldTensor_eq,
  GUT.HiggsQuarticFourMomentBasis.functional => Physics.HiggsQuarticFourMomentBasis.functional,
  GUT.HiggsQuarticFourMomentBasis.functional.eq_1 => Physics.HiggsQuarticFourMomentBasis.functional.eq_1,
  GUT.HiggsQuarticFourMomentBasis.internal => Physics.HiggsQuarticFourMomentBasis.internal,
  GUT.HiggsQuarticFourMomentBasis.internal_word => Physics.HiggsQuarticFourMomentBasis.internal_word,
  GUT.HiggsQuarticFourMomentBasis.momenta => Physics.HiggsQuarticFourMomentBasis.momenta,
  GUT.HiggsQuarticFourMomentBasis.momenta.eq_1 => Physics.HiggsQuarticFourMomentBasis.momenta.eq_1,
  GUT.HiggsQuarticFourMomentBasis.null => Physics.HiggsQuarticFourMomentBasis.null,
  GUT.HiggsQuarticFourMomentBasis.scale => Physics.HiggsQuarticFourMomentBasis.scale,
  GUT.HiggsQuarticFourMomentBasis.sum_moment => Physics.HiggsQuarticFourMomentBasis.sum_moment,
  GUT.HiggsQuarticFourMomentBasis.word_value => Physics.HiggsQuarticFourMomentBasis.word_value
]

assert_compatible GUT.HiggsQuarticFourMomentBasis.annihilates => Physics.HiggsQuarticFourMomentBasis.annihilates
assert_compatible GUT.HiggsQuarticFourMomentBasis.conservation => Physics.HiggsQuarticFourMomentBasis.conservation
assert_compatible GUT.HiggsQuarticFourMomentBasis.count => Physics.HiggsQuarticFourMomentBasis.count
assert_compatible GUT.HiggsQuarticFourMomentBasis.fieldModel => Physics.HiggsQuarticFourMomentBasis.fieldModel
assert_compatible GUT.HiggsQuarticFourMomentBasis.fieldModel.eq_1 => Physics.HiggsQuarticFourMomentBasis.fieldModel.eq_1
assert_compatible GUT.HiggsQuarticFourMomentBasis.fieldModel_invariant => Physics.HiggsQuarticFourMomentBasis.fieldModel_invariant
assert_compatible GUT.HiggsQuarticFourMomentBasis.fieldTensor_eq => Physics.HiggsQuarticFourMomentBasis.fieldTensor_eq
assert_compatible GUT.HiggsQuarticFourMomentBasis.functional => Physics.HiggsQuarticFourMomentBasis.functional
assert_compatible GUT.HiggsQuarticFourMomentBasis.functional.eq_1 => Physics.HiggsQuarticFourMomentBasis.functional.eq_1
assert_compatible GUT.HiggsQuarticFourMomentBasis.internal => Physics.HiggsQuarticFourMomentBasis.internal
assert_compatible GUT.HiggsQuarticFourMomentBasis.internal_word => Physics.HiggsQuarticFourMomentBasis.internal_word
assert_compatible GUT.HiggsQuarticFourMomentBasis.momenta => Physics.HiggsQuarticFourMomentBasis.momenta
assert_compatible GUT.HiggsQuarticFourMomentBasis.momenta.eq_1 => Physics.HiggsQuarticFourMomentBasis.momenta.eq_1
assert_compatible GUT.HiggsQuarticFourMomentBasis.null => Physics.HiggsQuarticFourMomentBasis.null
assert_compatible GUT.HiggsQuarticFourMomentBasis.scale => Physics.HiggsQuarticFourMomentBasis.scale
assert_compatible GUT.HiggsQuarticFourMomentBasis.sum_moment => Physics.HiggsQuarticFourMomentBasis.sum_moment
assert_compatible GUT.HiggsQuarticFourMomentBasis.word_value => Physics.HiggsQuarticFourMomentBasis.word_value
