import Physics.FieldTheory.Yukawa.Mass.VacuumMassProtection
import Physics.FieldTheory.Yukawa.WeylYukawaMass
import Physics.FieldTheory.Mass.InvariantMassProtection
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.VacuumMassProtection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.VacuumMassProtection.cross_apply => Physics.VacuumMassProtection.cross_apply,
  GUT.VacuumMassProtection.extends_iff => Physics.VacuumMassProtection.extends_iff,
  GUT.VacuumMassProtection.family_iff => Physics.VacuumMassProtection.family_iff,
  GUT.VacuumMassProtection.mass => Physics.VacuumMassProtection.mass,
  GUT.VacuumMassProtection.preserves_iff => Physics.VacuumMassProtection.preserves_iff,
  GUT.VacuumMassProtection.same_evaluation => Physics.VacuumMassProtection.same_evaluation
]

assert_compatible GUT.VacuumMassProtection.cross_apply => Physics.VacuumMassProtection.cross_apply
assert_compatible GUT.VacuumMassProtection.extends_iff => Physics.VacuumMassProtection.extends_iff
assert_compatible GUT.VacuumMassProtection.family_iff => Physics.VacuumMassProtection.family_iff
assert_compatible GUT.VacuumMassProtection.mass => Physics.VacuumMassProtection.mass
assert_compatible GUT.VacuumMassProtection.preserves_iff => Physics.VacuumMassProtection.preserves_iff
assert_compatible GUT.VacuumMassProtection.same_evaluation => Physics.VacuumMassProtection.same_evaluation
