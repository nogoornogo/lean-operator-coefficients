import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows3
import Physics.FieldTheory.Jets.LorentzRankFour.Rows2
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows3 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.row24 => Physics.LorentzRankFour.row24,
  GUT.LorentzRankFour.row25 => Physics.LorentzRankFour.row25,
  GUT.LorentzRankFour.row26 => Physics.LorentzRankFour.row26,
  GUT.LorentzRankFour.row27 => Physics.LorentzRankFour.row27,
  GUT.LorentzRankFour.row28 => Physics.LorentzRankFour.row28,
  GUT.LorentzRankFour.row29 => Physics.LorentzRankFour.row29,
  GUT.LorentzRankFour.row30 => Physics.LorentzRankFour.row30,
  GUT.LorentzRankFour.row31 => Physics.LorentzRankFour.row31
]

assert_compatible GUT.LorentzRankFour.row24 => Physics.LorentzRankFour.row24
assert_compatible GUT.LorentzRankFour.row25 => Physics.LorentzRankFour.row25
assert_compatible GUT.LorentzRankFour.row26 => Physics.LorentzRankFour.row26
assert_compatible GUT.LorentzRankFour.row27 => Physics.LorentzRankFour.row27
assert_compatible GUT.LorentzRankFour.row28 => Physics.LorentzRankFour.row28
assert_compatible GUT.LorentzRankFour.row29 => Physics.LorentzRankFour.row29
assert_compatible GUT.LorentzRankFour.row30 => Physics.LorentzRankFour.row30
assert_compatible GUT.LorentzRankFour.row31 => Physics.LorentzRankFour.row31
