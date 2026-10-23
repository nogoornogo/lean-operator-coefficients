import Physics.FieldTheory.Yukawa.Mass.SymmetricScalarYukawa
import Physics.FieldTheory.Yukawa.WeylYukawaMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.SymmetricScalarYukawa instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SymmetricScalarYukawa.Scalar => Physics.SymmetricScalarYukawa.Scalar,
  GUT.SymmetricScalarYukawa.bilinRho => Physics.SymmetricScalarYukawa.bilinRho,
  GUT.SymmetricScalarYukawa.bilinRho_apply => Physics.SymmetricScalarYukawa.bilinRho_apply,
  GUT.SymmetricScalarYukawa.fixed_iff => Physics.SymmetricScalarYukawa.fixed_iff,
  GUT.SymmetricScalarYukawa.inducedMass => Physics.SymmetricScalarYukawa.inducedMass,
  GUT.SymmetricScalarYukawa.inducedMass.eq_1 => Physics.SymmetricScalarYukawa.inducedMass.eq_1,
  GUT.SymmetricScalarYukawa.inducedMass_eq => Physics.SymmetricScalarYukawa.inducedMass_eq,
  GUT.SymmetricScalarYukawa.scalarRho => Physics.SymmetricScalarYukawa.scalarRho,
  GUT.SymmetricScalarYukawa.scalarRho_apply => Physics.SymmetricScalarYukawa.scalarRho_apply,
  GUT.SymmetricScalarYukawa.symmetricForms => Physics.SymmetricScalarYukawa.symmetricForms,
  GUT.SymmetricScalarYukawa.vacuum => Physics.SymmetricScalarYukawa.vacuum,
  GUT.SymmetricScalarYukawa.vacuum.eq_1 => Physics.SymmetricScalarYukawa.vacuum.eq_1,
  GUT.SymmetricScalarYukawa.vacuum_fixed => Physics.SymmetricScalarYukawa.vacuum_fixed,
  GUT.SymmetricScalarYukawa.vacuum_nonzero => Physics.SymmetricScalarYukawa.vacuum_nonzero,
  GUT.SymmetricScalarYukawa.yukawa => Physics.SymmetricScalarYukawa.yukawa,
  GUT.SymmetricScalarYukawa.yukawa.eq_1 => Physics.SymmetricScalarYukawa.yukawa.eq_1,
  GUT.SymmetricScalarYukawa.yukawa_apply => Physics.SymmetricScalarYukawa.yukawa_apply,
  GUT.WeylYukawaMass.atVacuumOn.eq_1 => Physics.WeylYukawaMass.atVacuumOn.eq_1
]

assert_compatible GUT.SymmetricScalarYukawa.Scalar => Physics.SymmetricScalarYukawa.Scalar
assert_compatible GUT.SymmetricScalarYukawa.bilinRho => Physics.SymmetricScalarYukawa.bilinRho
assert_compatible GUT.SymmetricScalarYukawa.bilinRho_apply => Physics.SymmetricScalarYukawa.bilinRho_apply
assert_compatible GUT.SymmetricScalarYukawa.fixed_iff => Physics.SymmetricScalarYukawa.fixed_iff
assert_compatible GUT.SymmetricScalarYukawa.inducedMass => Physics.SymmetricScalarYukawa.inducedMass
assert_compatible GUT.SymmetricScalarYukawa.inducedMass.eq_1 => Physics.SymmetricScalarYukawa.inducedMass.eq_1
assert_compatible GUT.SymmetricScalarYukawa.inducedMass_eq => Physics.SymmetricScalarYukawa.inducedMass_eq
assert_compatible GUT.SymmetricScalarYukawa.scalarRho => Physics.SymmetricScalarYukawa.scalarRho
assert_compatible GUT.SymmetricScalarYukawa.scalarRho_apply => Physics.SymmetricScalarYukawa.scalarRho_apply
assert_compatible GUT.SymmetricScalarYukawa.symmetricForms => Physics.SymmetricScalarYukawa.symmetricForms
assert_compatible GUT.SymmetricScalarYukawa.vacuum => Physics.SymmetricScalarYukawa.vacuum
assert_compatible GUT.SymmetricScalarYukawa.vacuum.eq_1 => Physics.SymmetricScalarYukawa.vacuum.eq_1
assert_compatible GUT.SymmetricScalarYukawa.vacuum_fixed => Physics.SymmetricScalarYukawa.vacuum_fixed
assert_compatible GUT.SymmetricScalarYukawa.vacuum_nonzero => Physics.SymmetricScalarYukawa.vacuum_nonzero
assert_compatible GUT.SymmetricScalarYukawa.yukawa => Physics.SymmetricScalarYukawa.yukawa
assert_compatible GUT.SymmetricScalarYukawa.yukawa.eq_1 => Physics.SymmetricScalarYukawa.yukawa.eq_1
assert_compatible GUT.SymmetricScalarYukawa.yukawa_apply => Physics.SymmetricScalarYukawa.yukawa_apply
assert_compatible GUT.WeylYukawaMass.atVacuumOn.eq_1 => Physics.WeylYukawaMass.atVacuumOn.eq_1
