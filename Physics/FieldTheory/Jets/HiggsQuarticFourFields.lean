import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourFields
import Physics.FieldTheory.Jets.HiggsQuarticFourTensors
import Math.Algebra.FourDerivativeWords
import Math.RepresentationTheory.ColoredWavePairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourFields instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFieldDictionary.action.eq_1 => Physics.HiggsFieldDictionary.action.eq_1,
  GUT.HiggsQuarticFourFields.Fields => Physics.HiggsQuarticFourFields.Fields,
  GUT.HiggsQuarticFourFields.T => Physics.HiggsQuarticFourFields.T,
  GUT.HiggsQuarticFourFields.fieldTensor => Physics.HiggsQuarticFourFields.fieldTensor,
  GUT.HiggsQuarticFourFields.fieldTensor_apply => Physics.HiggsQuarticFourFields.fieldTensor_apply,
  GUT.HiggsQuarticFourFields.fieldTensor_basis => Physics.HiggsQuarticFourFields.fieldTensor_basis,
  GUT.HiggsQuarticFourFields.fieldWord => Physics.HiggsQuarticFourFields.fieldWord,
  GUT.HiggsQuarticFourFields.fieldWord.eq_1 => Physics.HiggsQuarticFourFields.fieldWord.eq_1,
  GUT.HiggsQuarticFourFields.internal_basis => Physics.HiggsQuarticFourFields.internal_basis,
  GUT.HiggsQuarticFourFields.internal_covariant => Physics.HiggsQuarticFourFields.internal_covariant,
  GUT.HiggsQuarticFourFields.multilinear_ext => Physics.HiggsQuarticFourFields.multilinear_ext,
  GUT.HiggsQuarticFourFields.word_basis => Physics.HiggsQuarticFourFields.word_basis
]

assert_compatible GUT.HiggsFieldDictionary.action.eq_1 => Physics.HiggsFieldDictionary.action.eq_1
assert_compatible GUT.HiggsQuarticFourFields.Fields => Physics.HiggsQuarticFourFields.Fields
assert_compatible GUT.HiggsQuarticFourFields.T => Physics.HiggsQuarticFourFields.T
assert_compatible GUT.HiggsQuarticFourFields.fieldTensor => Physics.HiggsQuarticFourFields.fieldTensor
assert_compatible GUT.HiggsQuarticFourFields.fieldTensor_apply => Physics.HiggsQuarticFourFields.fieldTensor_apply
assert_compatible GUT.HiggsQuarticFourFields.fieldTensor_basis => Physics.HiggsQuarticFourFields.fieldTensor_basis
assert_compatible GUT.HiggsQuarticFourFields.fieldWord => Physics.HiggsQuarticFourFields.fieldWord
assert_compatible GUT.HiggsQuarticFourFields.fieldWord.eq_1 => Physics.HiggsQuarticFourFields.fieldWord.eq_1
assert_compatible GUT.HiggsQuarticFourFields.internal_basis => Physics.HiggsQuarticFourFields.internal_basis
assert_compatible GUT.HiggsQuarticFourFields.internal_covariant => Physics.HiggsQuarticFourFields.internal_covariant
assert_compatible GUT.HiggsQuarticFourFields.multilinear_ext => Physics.HiggsQuarticFourFields.multilinear_ext
assert_compatible GUT.HiggsQuarticFourFields.word_basis => Physics.HiggsQuarticFourFields.word_basis
