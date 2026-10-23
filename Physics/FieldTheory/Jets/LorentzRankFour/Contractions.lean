import Physics.FieldTheory.Jets.LorentzRankFour.Core.Contractions
import Physics.FieldTheory.Jets.LorentzRankFour
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Contractions instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.crossTrace => Physics.LorentzRankFour.crossTrace,
  GUT.LorentzRankFour.doubleTrace => Physics.LorentzRankFour.doubleTrace,
  GUT.LorentzRankFour.eta => Physics.LorentzRankFour.eta,
  GUT.LorentzRankFour.trace00 => Physics.LorentzRankFour.trace00,
  GUT.LorentzRankFour.zero_of_double_trace_and_symmetric => Physics.LorentzRankFour.zero_of_double_trace_and_symmetric,
  GUT.LorentzRankFour.zero_of_trace_and_cross => Physics.LorentzRankFour.zero_of_trace_and_cross,
  GUT.LorentzRankFour.zero_of_trace_and_symmetric => Physics.LorentzRankFour.zero_of_trace_and_symmetric
]

assert_compatible GUT.LorentzRankFour.crossTrace => Physics.LorentzRankFour.crossTrace
assert_compatible GUT.LorentzRankFour.doubleTrace => Physics.LorentzRankFour.doubleTrace
assert_compatible GUT.LorentzRankFour.eta => Physics.LorentzRankFour.eta
assert_compatible GUT.LorentzRankFour.trace00 => Physics.LorentzRankFour.trace00
assert_compatible GUT.LorentzRankFour.zero_of_double_trace_and_symmetric => Physics.LorentzRankFour.zero_of_double_trace_and_symmetric
assert_compatible GUT.LorentzRankFour.zero_of_trace_and_cross => Physics.LorentzRankFour.zero_of_trace_and_cross
assert_compatible GUT.LorentzRankFour.zero_of_trace_and_symmetric => Physics.LorentzRankFour.zero_of_trace_and_symmetric
