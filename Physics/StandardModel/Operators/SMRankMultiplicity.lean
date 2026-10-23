import Physics.StandardModel.Operators.Support.Coordinates.SMRankMultiplicity
import Math.RepresentationTheory.PatternMultiplicityEquiv
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMRankMultiplicity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMRankMultiplicity.actionEquiv => Physics.SMRankMultiplicity.actionEquiv,
  GUT.SMRankMultiplicity.kernelEquiv => Physics.SMRankMultiplicity.kernelEquiv,
  GUT.SMRankMultiplicity.rank_eq => Physics.SMRankMultiplicity.rank_eq,
  GUT.SMRankMultiplicity.sourceEquiv => Physics.SMRankMultiplicity.sourceEquiv
]

assert_compatible GUT.SMRankMultiplicity.actionEquiv => Physics.SMRankMultiplicity.actionEquiv
assert_compatible GUT.SMRankMultiplicity.kernelEquiv => Physics.SMRankMultiplicity.kernelEquiv
assert_compatible GUT.SMRankMultiplicity.rank_eq => Physics.SMRankMultiplicity.rank_eq
assert_compatible GUT.SMRankMultiplicity.sourceEquiv => Physics.SMRankMultiplicity.sourceEquiv
