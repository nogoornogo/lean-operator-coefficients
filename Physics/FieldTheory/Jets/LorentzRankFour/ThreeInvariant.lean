import Physics.FieldTheory.Jets.LorentzRankFour.Core.ThreeInvariant
import Physics.FieldTheory.Jets.LorentzRankFour.Invariant
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.ThreeInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFourThree.double_trace => Physics.LorentzRankFourThree.double_trace,
  GUT.LorentzRankFourThree.invariant_of_components => Physics.LorentzRankFourThree.invariant_of_components,
  GUT.LorentzRankFourThree.reconstruct => Physics.LorentzRankFourThree.reconstruct
]

assert_compatible GUT.LorentzRankFourThree.double_trace => Physics.LorentzRankFourThree.double_trace
assert_compatible GUT.LorentzRankFourThree.invariant_of_components => Physics.LorentzRankFourThree.invariant_of_components
assert_compatible GUT.LorentzRankFourThree.reconstruct => Physics.LorentzRankFourThree.reconstruct
