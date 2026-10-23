import Physics.StandardModel.Operators.Higgs.FullHiggsCoefficientBridge
import Math.RepresentationTheory.TwoSpeciesCoefficientBridge
import Physics.StandardModel.Operators.HiggsPatternDescent
import Physics.StandardModel.Operators.SMHiggsConstituents
import Physics.StandardModel.Operators.WeakSingletHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.FullHiggsCoefficientBridge instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FullHiggsCoefficientBridge.Space => Physics.FullHiggsCoefficientBridge.Space,
  GUT.FullHiggsCoefficientBridge.allowed_iff => Physics.FullHiggsCoefficientBridge.allowed_iff,
  GUT.FullHiggsCoefficientBridge.bosonsEquiv => Physics.FullHiggsCoefficientBridge.bosonsEquiv,
  GUT.FullHiggsCoefficientBridge.constituentEquiv => Physics.FullHiggsCoefficientBridge.constituentEquiv,
  GUT.FullHiggsCoefficientBridge.forbidden_iff => Physics.FullHiggsCoefficientBridge.forbidden_iff,
  GUT.FullHiggsCoefficientBridge.leftEquiv => Physics.FullHiggsCoefficientBridge.leftEquiv,
  GUT.FullHiggsCoefficientBridge.matterEquiv => Physics.FullHiggsCoefficientBridge.matterEquiv,
  GUT.FullHiggsCoefficientBridge.mem_space_iff => Physics.FullHiggsCoefficientBridge.mem_space_iff,
  GUT.FullHiggsCoefficientBridge.rightEquiv => Physics.FullHiggsCoefficientBridge.rightEquiv,
  GUT.FullHiggsCoefficientBridge.splitEquiv => Physics.FullHiggsCoefficientBridge.splitEquiv,
  GUT.FullHiggsCoefficientBridge.weakSinglet_allowed_iff => Physics.FullHiggsCoefficientBridge.weakSinglet_allowed_iff
]

assert_compatible GUT.FullHiggsCoefficientBridge.Space => Physics.FullHiggsCoefficientBridge.Space
assert_compatible GUT.FullHiggsCoefficientBridge.allowed_iff => Physics.FullHiggsCoefficientBridge.allowed_iff
assert_compatible GUT.FullHiggsCoefficientBridge.bosonsEquiv => Physics.FullHiggsCoefficientBridge.bosonsEquiv
assert_compatible GUT.FullHiggsCoefficientBridge.constituentEquiv => Physics.FullHiggsCoefficientBridge.constituentEquiv
assert_compatible GUT.FullHiggsCoefficientBridge.forbidden_iff => Physics.FullHiggsCoefficientBridge.forbidden_iff
assert_compatible GUT.FullHiggsCoefficientBridge.leftEquiv => Physics.FullHiggsCoefficientBridge.leftEquiv
assert_compatible GUT.FullHiggsCoefficientBridge.matterEquiv => Physics.FullHiggsCoefficientBridge.matterEquiv
assert_compatible GUT.FullHiggsCoefficientBridge.mem_space_iff => Physics.FullHiggsCoefficientBridge.mem_space_iff
assert_compatible GUT.FullHiggsCoefficientBridge.rightEquiv => Physics.FullHiggsCoefficientBridge.rightEquiv
assert_compatible GUT.FullHiggsCoefficientBridge.splitEquiv => Physics.FullHiggsCoefficientBridge.splitEquiv
assert_compatible GUT.FullHiggsCoefficientBridge.weakSinglet_allowed_iff => Physics.FullHiggsCoefficientBridge.weakSinglet_allowed_iff
