import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows4
import Physics.FieldTheory.Jets.LorentzRankFour.Rows3
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows4 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.row32 => Physics.LorentzRankFour.row32,
  GUT.LorentzRankFour.row33 => Physics.LorentzRankFour.row33,
  GUT.LorentzRankFour.row34 => Physics.LorentzRankFour.row34,
  GUT.LorentzRankFour.row35 => Physics.LorentzRankFour.row35,
  GUT.LorentzRankFour.row36 => Physics.LorentzRankFour.row36,
  GUT.LorentzRankFour.row37 => Physics.LorentzRankFour.row37
]

assert_compatible GUT.LorentzRankFour.row32 => Physics.LorentzRankFour.row32
assert_compatible GUT.LorentzRankFour.row33 => Physics.LorentzRankFour.row33
assert_compatible GUT.LorentzRankFour.row34 => Physics.LorentzRankFour.row34
assert_compatible GUT.LorentzRankFour.row35 => Physics.LorentzRankFour.row35
assert_compatible GUT.LorentzRankFour.row36 => Physics.LorentzRankFour.row36
assert_compatible GUT.LorentzRankFour.row37 => Physics.LorentzRankFour.row37
