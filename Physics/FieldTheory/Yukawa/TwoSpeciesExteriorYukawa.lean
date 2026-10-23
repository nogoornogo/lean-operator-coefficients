import Physics.FieldTheory.Yukawa.Mass.TwoSpeciesExteriorYukawa
import Math.RepresentationTheory.ExternalInvariantTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.TwoSpeciesExteriorYukawa instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.TwoSpeciesExteriorYukawa.alternating => Physics.TwoSpeciesExteriorYukawa.alternating,
  GUT.TwoSpeciesExteriorYukawa.alternating.eq_1 => Physics.TwoSpeciesExteriorYukawa.alternating.eq_1,
  GUT.TwoSpeciesExteriorYukawa.coefficient => Physics.TwoSpeciesExteriorYukawa.coefficient,
  GUT.TwoSpeciesExteriorYukawa.coefficient.eq_1 => Physics.TwoSpeciesExteriorYukawa.coefficient.eq_1,
  GUT.TwoSpeciesExteriorYukawa.nonzero => Physics.TwoSpeciesExteriorYukawa.nonzero,
  GUT.TwoSpeciesExteriorYukawa.ordered => Physics.TwoSpeciesExteriorYukawa.ordered,
  GUT.TwoSpeciesExteriorYukawa.ordered.eq_1 => Physics.TwoSpeciesExteriorYukawa.ordered.eq_1,
  GUT.TwoSpeciesExteriorYukawa.slots => Physics.TwoSpeciesExteriorYukawa.slots
]

assert_compatible GUT.TwoSpeciesExteriorYukawa.alternating => Physics.TwoSpeciesExteriorYukawa.alternating
assert_compatible GUT.TwoSpeciesExteriorYukawa.alternating.eq_1 => Physics.TwoSpeciesExteriorYukawa.alternating.eq_1
assert_compatible GUT.TwoSpeciesExteriorYukawa.coefficient => Physics.TwoSpeciesExteriorYukawa.coefficient
assert_compatible GUT.TwoSpeciesExteriorYukawa.coefficient.eq_1 => Physics.TwoSpeciesExteriorYukawa.coefficient.eq_1
assert_compatible GUT.TwoSpeciesExteriorYukawa.nonzero => Physics.TwoSpeciesExteriorYukawa.nonzero
assert_compatible GUT.TwoSpeciesExteriorYukawa.ordered => Physics.TwoSpeciesExteriorYukawa.ordered
assert_compatible GUT.TwoSpeciesExteriorYukawa.ordered.eq_1 => Physics.TwoSpeciesExteriorYukawa.ordered.eq_1
assert_compatible GUT.TwoSpeciesExteriorYukawa.slots => Physics.TwoSpeciesExteriorYukawa.slots
