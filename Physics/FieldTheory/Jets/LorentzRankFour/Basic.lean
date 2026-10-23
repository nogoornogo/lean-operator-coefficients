import Physics.FieldTheory.Jets.LorentzRankFour.Core.Basic
import Physics.FieldTheory.Jets.LorentzFiniteControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.LorentzRankFour.Core.Basic instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzRankFour.Dir => Physics.LorentzRankFour.Dir,
  GUT.LorentzRankFour.Tensor => Physics.LorentzRankFour.Tensor,
  GUT.LorentzRankFour.component => Physics.LorentzRankFour.component,
  GUT.LorentzRankFour.component.eq_1 => Physics.LorentzRankFour.component.eq_1,
  GUT.LorentzRankFour.component_apply => Physics.LorentzRankFour.component_apply,
  GUT.LorentzRankFour.killed => Physics.LorentzRankFour.killed,
  GUT.LorentzRankFour.killed_zero => Physics.LorentzRankFour.killed_zero,
  GUT.LorentzRankFour.normalComponent => Physics.LorentzRankFour.normalComponent,
  GUT.LorentzRankFour.normalize => Physics.LorentzRankFour.normalize
]

assert_compatible GUT.LorentzRankFour.Dir => Physics.LorentzRankFour.Dir
assert_compatible GUT.LorentzRankFour.Tensor => Physics.LorentzRankFour.Tensor
assert_compatible GUT.LorentzRankFour.component => Physics.LorentzRankFour.component
assert_compatible GUT.LorentzRankFour.component.eq_1 => Physics.LorentzRankFour.component.eq_1
assert_compatible GUT.LorentzRankFour.component_apply => Physics.LorentzRankFour.component_apply
assert_compatible GUT.LorentzRankFour.killed => Physics.LorentzRankFour.killed
assert_compatible GUT.LorentzRankFour.killed_zero => Physics.LorentzRankFour.killed_zero
assert_compatible GUT.LorentzRankFour.normalComponent => Physics.LorentzRankFour.normalComponent
assert_compatible GUT.LorentzRankFour.normalize => Physics.LorentzRankFour.normalize
