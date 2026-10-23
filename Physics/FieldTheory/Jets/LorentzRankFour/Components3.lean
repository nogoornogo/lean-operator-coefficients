import Physics.FieldTheory.Jets.LorentzRankFour.Core.Components3
import Physics.FieldTheory.Jets.LorentzRankFour.Components2
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Components3 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.components30 => Physics.LorentzRankFour.components30,
  GUT.LorentzRankFour.components31 => Physics.LorentzRankFour.components31,
  GUT.LorentzRankFour.components32 => Physics.LorentzRankFour.components32,
  GUT.LorentzRankFour.components33 => Physics.LorentzRankFour.components33
]

assert_compatible GUT.LorentzRankFour.components30 => Physics.LorentzRankFour.components30
assert_compatible GUT.LorentzRankFour.components31 => Physics.LorentzRankFour.components31
assert_compatible GUT.LorentzRankFour.components32 => Physics.LorentzRankFour.components32
assert_compatible GUT.LorentzRankFour.components33 => Physics.LorentzRankFour.components33
