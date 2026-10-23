import Physics.FieldTheory.Mass.Algebra.LightInheritanceBoundary
import Physics.FieldTheory.Mass.InvariantWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.LightInheritanceBoundary instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LightInheritanceBoundary.light_not_preserved => Physics.LightInheritanceBoundary.light_not_preserved,
  GUT.LightInheritanceBoundary.pairedMass => Physics.LightInheritanceBoundary.pairedMass,
  GUT.LightInheritanceBoundary.paired_mem_radical_iff => Physics.LightInheritanceBoundary.paired_mem_radical_iff,
  GUT.LightInheritanceBoundary.paired_radical_eq_bot => Physics.LightInheritanceBoundary.paired_radical_eq_bot,
  GUT.LightInheritanceBoundary.restricted_mass_eq => Physics.LightInheritanceBoundary.restricted_mass_eq,
  GUT.LightInheritanceBoundary.retained => Physics.LightInheritanceBoundary.retained,
  GUT.LightInheritanceBoundary.retained_injective => Physics.LightInheritanceBoundary.retained_injective
]

assert_compatible GUT.LightInheritanceBoundary.light_not_preserved => Physics.LightInheritanceBoundary.light_not_preserved
assert_compatible GUT.LightInheritanceBoundary.pairedMass => Physics.LightInheritanceBoundary.pairedMass
assert_compatible GUT.LightInheritanceBoundary.paired_mem_radical_iff => Physics.LightInheritanceBoundary.paired_mem_radical_iff
assert_compatible GUT.LightInheritanceBoundary.paired_radical_eq_bot => Physics.LightInheritanceBoundary.paired_radical_eq_bot
assert_compatible GUT.LightInheritanceBoundary.restricted_mass_eq => Physics.LightInheritanceBoundary.restricted_mass_eq
assert_compatible GUT.LightInheritanceBoundary.retained => Physics.LightInheritanceBoundary.retained
assert_compatible GUT.LightInheritanceBoundary.retained_injective => Physics.LightInheritanceBoundary.retained_injective
