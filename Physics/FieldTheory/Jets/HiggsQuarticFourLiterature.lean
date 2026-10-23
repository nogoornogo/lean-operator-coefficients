import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiterature
import Physics.FieldTheory.Jets.HiggsQuarticFourCompleteness
import Physics.FieldTheory.Jets.HiggsQuarticFourLiInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiterature instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourLiterature.eboliCoordinate => Physics.HiggsQuarticFourLiterature.eboliCoordinate,
  GUT.HiggsQuarticFourLiterature.eboliEquivalence => Physics.HiggsQuarticFourLiterature.eboliEquivalence,
  GUT.HiggsQuarticFourLiterature.eboliNative => Physics.HiggsQuarticFourLiterature.eboliNative,
  GUT.HiggsQuarticFourLiterature.eboliOrder => Physics.HiggsQuarticFourLiterature.eboliOrder,
  GUT.HiggsQuarticFourLiterature.eboli_coordinate_apply => Physics.HiggsQuarticFourLiterature.eboli_coordinate_apply,
  GUT.HiggsQuarticFourLiterature.eboli_extraction => Physics.HiggsQuarticFourLiterature.eboli_extraction,
  GUT.HiggsQuarticFourLiterature.liEquivalence => Physics.HiggsQuarticFourLiterature.liEquivalence,
  GUT.HiggsQuarticFourLiterature.li_extraction => Physics.HiggsQuarticFourLiterature.li_extraction,
  GUT.HiggsQuarticFourLiterature.murphyEquivalence => Physics.HiggsQuarticFourLiterature.murphyEquivalence,
  GUT.HiggsQuarticFourLiterature.murphy_extraction => Physics.HiggsQuarticFourLiterature.murphy_extraction,
  GUT.HiggsQuarticFourLiterature.omitted_S2 => Physics.HiggsQuarticFourLiterature.omitted_S2
]

assert_compatible GUT.HiggsQuarticFourLiterature.eboliCoordinate => Physics.HiggsQuarticFourLiterature.eboliCoordinate
assert_compatible GUT.HiggsQuarticFourLiterature.eboliEquivalence => Physics.HiggsQuarticFourLiterature.eboliEquivalence
assert_compatible GUT.HiggsQuarticFourLiterature.eboliNative => Physics.HiggsQuarticFourLiterature.eboliNative
assert_compatible GUT.HiggsQuarticFourLiterature.eboliOrder => Physics.HiggsQuarticFourLiterature.eboliOrder
assert_compatible GUT.HiggsQuarticFourLiterature.eboli_coordinate_apply => Physics.HiggsQuarticFourLiterature.eboli_coordinate_apply
assert_compatible GUT.HiggsQuarticFourLiterature.eboli_extraction => Physics.HiggsQuarticFourLiterature.eboli_extraction
assert_compatible GUT.HiggsQuarticFourLiterature.liEquivalence => Physics.HiggsQuarticFourLiterature.liEquivalence
assert_compatible GUT.HiggsQuarticFourLiterature.li_extraction => Physics.HiggsQuarticFourLiterature.li_extraction
assert_compatible GUT.HiggsQuarticFourLiterature.murphyEquivalence => Physics.HiggsQuarticFourLiterature.murphyEquivalence
assert_compatible GUT.HiggsQuarticFourLiterature.murphy_extraction => Physics.HiggsQuarticFourLiterature.murphy_extraction
assert_compatible GUT.HiggsQuarticFourLiterature.omitted_S2 => Physics.HiggsQuarticFourLiterature.omitted_S2
