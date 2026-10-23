import Physics.FieldTheory.Jets.LorentzRankFour.Core.Components1
import Physics.FieldTheory.Jets.LorentzRankFour.Components0
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Components1 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.components10 => Physics.LorentzRankFour.components10,
  GUT.LorentzRankFour.components11 => Physics.LorentzRankFour.components11,
  GUT.LorentzRankFour.components12 => Physics.LorentzRankFour.components12,
  GUT.LorentzRankFour.components13 => Physics.LorentzRankFour.components13
]

assert_compatible GUT.LorentzRankFour.components10 => Physics.LorentzRankFour.components10
assert_compatible GUT.LorentzRankFour.components11 => Physics.LorentzRankFour.components11
assert_compatible GUT.LorentzRankFour.components12 => Physics.LorentzRankFour.components12
assert_compatible GUT.LorentzRankFour.components13 => Physics.LorentzRankFour.components13
