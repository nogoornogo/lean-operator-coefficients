import Physics.FieldTheory.Jets.LorentzRankFour.Core.Components0
import Physics.FieldTheory.Jets.LorentzRankFour.Values
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Components0 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.components00 => Physics.LorentzRankFour.components00,
  GUT.LorentzRankFour.components01 => Physics.LorentzRankFour.components01,
  GUT.LorentzRankFour.components02 => Physics.LorentzRankFour.components02,
  GUT.LorentzRankFour.components03 => Physics.LorentzRankFour.components03,
  GUT.LorentzRankFour.metric => Physics.LorentzRankFour.metric,
  GUT.LorentzRankFour.metric.eq_1 => Physics.LorentzRankFour.metric.eq_1
]

assert_compatible GUT.LorentzRankFour.components00 => Physics.LorentzRankFour.components00
assert_compatible GUT.LorentzRankFour.components01 => Physics.LorentzRankFour.components01
assert_compatible GUT.LorentzRankFour.components02 => Physics.LorentzRankFour.components02
assert_compatible GUT.LorentzRankFour.components03 => Physics.LorentzRankFour.components03
assert_compatible GUT.LorentzRankFour.metric => Physics.LorentzRankFour.metric
assert_compatible GUT.LorentzRankFour.metric.eq_1 => Physics.LorentzRankFour.metric.eq_1
