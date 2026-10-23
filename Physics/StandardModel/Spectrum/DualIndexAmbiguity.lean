import Physics.StandardModel.Spectrum.Representations.DualIndexAmbiguity
import Physics.StandardModel.Spectrum.HyperchargeReversalProbe
import Math.RepresentationTheory.DualIndexCompatibility
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.DualIndexAmbiguity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMDualIndexAmbiguity.enlargedGeneration => Physics.SMDualIndexAmbiguity.enlargedGeneration,
  GUT.SMDualIndexAmbiguity.enlarged_character_one => Physics.SMDualIndexAmbiguity.enlarged_character_one,
  GUT.SMDualIndexAmbiguity.equal_dual_index => Physics.SMDualIndexAmbiguity.equal_dual_index,
  GUT.SMDualIndexAmbiguity.generation_character_one => Physics.SMDualIndexAmbiguity.generation_character_one,
  GUT.SMDualIndexAmbiguity.not_equiv => Physics.SMDualIndexAmbiguity.not_equiv
]

assert_compatible GUT.SMDualIndexAmbiguity.enlargedGeneration => Physics.SMDualIndexAmbiguity.enlargedGeneration
assert_compatible GUT.SMDualIndexAmbiguity.enlarged_character_one => Physics.SMDualIndexAmbiguity.enlarged_character_one
assert_compatible GUT.SMDualIndexAmbiguity.equal_dual_index => Physics.SMDualIndexAmbiguity.equal_dual_index
assert_compatible GUT.SMDualIndexAmbiguity.generation_character_one => Physics.SMDualIndexAmbiguity.generation_character_one
assert_compatible GUT.SMDualIndexAmbiguity.not_equiv => Physics.SMDualIndexAmbiguity.not_equiv
