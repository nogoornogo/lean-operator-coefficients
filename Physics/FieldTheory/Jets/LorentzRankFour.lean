import Physics.FieldTheory.Jets.Lorentz.LorentzRankFour
import Physics.FieldTheory.Jets.LorentzRankFour.Components3
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lorentz.LorentzRankFour instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.components => Physics.LorentzRankFour.components
]

assert_compatible GUT.LorentzRankFour.components => Physics.LorentzRankFour.components
