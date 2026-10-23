import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows0
import Physics.FieldTheory.Jets.LorentzRankFour.Basic
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows0 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.killed.eq_1 => Physics.LorentzRankFour.killed.eq_1,
  GUT.LorentzRankFour.normalComponent.eq_1 => Physics.LorentzRankFour.normalComponent.eq_1,
  GUT.LorentzRankFour.row0 => Physics.LorentzRankFour.row0,
  GUT.LorentzRankFour.row1 => Physics.LorentzRankFour.row1,
  GUT.LorentzRankFour.row2 => Physics.LorentzRankFour.row2,
  GUT.LorentzRankFour.row3 => Physics.LorentzRankFour.row3,
  GUT.LorentzRankFour.row4 => Physics.LorentzRankFour.row4,
  GUT.LorentzRankFour.row5 => Physics.LorentzRankFour.row5,
  GUT.LorentzRankFour.row6 => Physics.LorentzRankFour.row6,
  GUT.LorentzRankFour.row7 => Physics.LorentzRankFour.row7
]

assert_compatible GUT.LorentzRankFour.killed.eq_1 => Physics.LorentzRankFour.killed.eq_1
assert_compatible GUT.LorentzRankFour.normalComponent.eq_1 => Physics.LorentzRankFour.normalComponent.eq_1
assert_compatible GUT.LorentzRankFour.row0 => Physics.LorentzRankFour.row0
assert_compatible GUT.LorentzRankFour.row1 => Physics.LorentzRankFour.row1
assert_compatible GUT.LorentzRankFour.row2 => Physics.LorentzRankFour.row2
assert_compatible GUT.LorentzRankFour.row3 => Physics.LorentzRankFour.row3
assert_compatible GUT.LorentzRankFour.row4 => Physics.LorentzRankFour.row4
assert_compatible GUT.LorentzRankFour.row5 => Physics.LorentzRankFour.row5
assert_compatible GUT.LorentzRankFour.row6 => Physics.LorentzRankFour.row6
assert_compatible GUT.LorentzRankFour.row7 => Physics.LorentzRankFour.row7
