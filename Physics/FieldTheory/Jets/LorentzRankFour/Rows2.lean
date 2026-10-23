import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows2
import Physics.FieldTheory.Jets.LorentzRankFour.Rows1
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows2 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.row16 => Physics.LorentzRankFour.row16,
  GUT.LorentzRankFour.row17 => Physics.LorentzRankFour.row17,
  GUT.LorentzRankFour.row18 => Physics.LorentzRankFour.row18,
  GUT.LorentzRankFour.row19 => Physics.LorentzRankFour.row19,
  GUT.LorentzRankFour.row20 => Physics.LorentzRankFour.row20,
  GUT.LorentzRankFour.row21 => Physics.LorentzRankFour.row21,
  GUT.LorentzRankFour.row22 => Physics.LorentzRankFour.row22,
  GUT.LorentzRankFour.row23 => Physics.LorentzRankFour.row23
]

assert_compatible GUT.LorentzRankFour.row16 => Physics.LorentzRankFour.row16
assert_compatible GUT.LorentzRankFour.row17 => Physics.LorentzRankFour.row17
assert_compatible GUT.LorentzRankFour.row18 => Physics.LorentzRankFour.row18
assert_compatible GUT.LorentzRankFour.row19 => Physics.LorentzRankFour.row19
assert_compatible GUT.LorentzRankFour.row20 => Physics.LorentzRankFour.row20
assert_compatible GUT.LorentzRankFour.row21 => Physics.LorentzRankFour.row21
assert_compatible GUT.LorentzRankFour.row22 => Physics.LorentzRankFour.row22
assert_compatible GUT.LorentzRankFour.row23 => Physics.LorentzRankFour.row23
