import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows1
import Physics.FieldTheory.Jets.LorentzRankFour.Rows0
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows1 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.row10 => Physics.LorentzRankFour.row10,
  GUT.LorentzRankFour.row11 => Physics.LorentzRankFour.row11,
  GUT.LorentzRankFour.row12 => Physics.LorentzRankFour.row12,
  GUT.LorentzRankFour.row13 => Physics.LorentzRankFour.row13,
  GUT.LorentzRankFour.row14 => Physics.LorentzRankFour.row14,
  GUT.LorentzRankFour.row15 => Physics.LorentzRankFour.row15,
  GUT.LorentzRankFour.row8 => Physics.LorentzRankFour.row8,
  GUT.LorentzRankFour.row9 => Physics.LorentzRankFour.row9
]

assert_compatible GUT.LorentzRankFour.row10 => Physics.LorentzRankFour.row10
assert_compatible GUT.LorentzRankFour.row11 => Physics.LorentzRankFour.row11
assert_compatible GUT.LorentzRankFour.row12 => Physics.LorentzRankFour.row12
assert_compatible GUT.LorentzRankFour.row13 => Physics.LorentzRankFour.row13
assert_compatible GUT.LorentzRankFour.row14 => Physics.LorentzRankFour.row14
assert_compatible GUT.LorentzRankFour.row15 => Physics.LorentzRankFour.row15
assert_compatible GUT.LorentzRankFour.row8 => Physics.LorentzRankFour.row8
assert_compatible GUT.LorentzRankFour.row9 => Physics.LorentzRankFour.row9
