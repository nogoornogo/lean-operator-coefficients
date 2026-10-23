import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarDerivativeInterface
import Math.RepresentationTheory.DerivativeInterface
import Physics.FieldTheory.Jets.ScalarInputAdapter
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarDerivativeInterface instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarDerivativeInterface.compatibleInput => Physics.ScalarDerivativeInterface.compatibleInput,
  GUT.ScalarDerivativeInterface.compatible_map => Physics.ScalarDerivativeInterface.compatible_map,
  GUT.ScalarDerivativeInterface.cubic => Physics.ScalarDerivativeInterface.cubic,
  GUT.ScalarDerivativeInterface.cubic_mem => Physics.ScalarDerivativeInterface.cubic_mem,
  GUT.ScalarDerivativeInterface.interactionSource => Physics.ScalarDerivativeInterface.interactionSource,
  GUT.ScalarDerivativeInterface.interaction_stable => Physics.ScalarDerivativeInterface.interaction_stable,
  GUT.ScalarDerivativeInterface.restriction_agrees => Physics.ScalarDerivativeInterface.restriction_agrees,
  GUT.ScalarDerivativeInterface.scalar => Physics.ScalarDerivativeInterface.scalar,
  GUT.ScalarDerivativeInterface.scalar_extraction => Physics.ScalarDerivativeInterface.scalar_extraction,
  GUT.ScalarDerivativeInterface.seed_mem_source => Physics.ScalarDerivativeInterface.seed_mem_source,
  GUT.ScalarDerivativeInterface.selected => Physics.ScalarDerivativeInterface.selected,
  GUT.ScalarDerivativeInterface.selectedImageEquiv => Physics.ScalarDerivativeInterface.selectedImageEquiv,
  GUT.ScalarDerivativeInterface.selectedSeed => Physics.ScalarDerivativeInterface.selectedSeed,
  GUT.ScalarDerivativeInterface.selected_interaction => Physics.ScalarDerivativeInterface.selected_interaction,
  GUT.ScalarDerivativeInterface.selected_seed_relation => Physics.ScalarDerivativeInterface.selected_seed_relation,
  GUT.ScalarDerivativeInterface.wave => Physics.ScalarDerivativeInterface.wave,
  GUT.ScalarDerivativeInterface.wave_mem => Physics.ScalarDerivativeInterface.wave_mem
]

assert_compatible GUT.ScalarDerivativeInterface.compatibleInput => Physics.ScalarDerivativeInterface.compatibleInput
assert_compatible GUT.ScalarDerivativeInterface.compatible_map => Physics.ScalarDerivativeInterface.compatible_map
assert_compatible GUT.ScalarDerivativeInterface.cubic => Physics.ScalarDerivativeInterface.cubic
assert_compatible GUT.ScalarDerivativeInterface.cubic_mem => Physics.ScalarDerivativeInterface.cubic_mem
assert_compatible GUT.ScalarDerivativeInterface.interactionSource => Physics.ScalarDerivativeInterface.interactionSource
assert_compatible GUT.ScalarDerivativeInterface.interaction_stable => Physics.ScalarDerivativeInterface.interaction_stable
assert_compatible GUT.ScalarDerivativeInterface.restriction_agrees => Physics.ScalarDerivativeInterface.restriction_agrees
assert_compatible GUT.ScalarDerivativeInterface.scalar => Physics.ScalarDerivativeInterface.scalar
assert_compatible GUT.ScalarDerivativeInterface.scalar_extraction => Physics.ScalarDerivativeInterface.scalar_extraction
assert_compatible GUT.ScalarDerivativeInterface.seed_mem_source => Physics.ScalarDerivativeInterface.seed_mem_source
assert_compatible GUT.ScalarDerivativeInterface.selected => Physics.ScalarDerivativeInterface.selected
assert_compatible GUT.ScalarDerivativeInterface.selectedImageEquiv => Physics.ScalarDerivativeInterface.selectedImageEquiv
assert_compatible GUT.ScalarDerivativeInterface.selectedSeed => Physics.ScalarDerivativeInterface.selectedSeed
assert_compatible GUT.ScalarDerivativeInterface.selected_interaction => Physics.ScalarDerivativeInterface.selected_interaction
assert_compatible GUT.ScalarDerivativeInterface.selected_seed_relation => Physics.ScalarDerivativeInterface.selected_seed_relation
assert_compatible GUT.ScalarDerivativeInterface.wave => Physics.ScalarDerivativeInterface.wave
assert_compatible GUT.ScalarDerivativeInterface.wave_mem => Physics.ScalarDerivativeInterface.wave_mem
