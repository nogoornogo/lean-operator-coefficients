import Physics.FieldTheory.Jets.LorentzRankFour.Core.Components2
import Physics.FieldTheory.Jets.LorentzRankFour.Components1
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Components2 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.components20 => Physics.LorentzRankFour.components20,
  GUT.LorentzRankFour.components21 => Physics.LorentzRankFour.components21,
  GUT.LorentzRankFour.components22 => Physics.LorentzRankFour.components22,
  GUT.LorentzRankFour.components23 => Physics.LorentzRankFour.components23
]

assert_compatible GUT.LorentzRankFour.components20 => Physics.LorentzRankFour.components20
assert_compatible GUT.LorentzRankFour.components21 => Physics.LorentzRankFour.components21
assert_compatible GUT.LorentzRankFour.components22 => Physics.LorentzRankFour.components22
assert_compatible GUT.LorentzRankFour.components23 => Physics.LorentzRankFour.components23
