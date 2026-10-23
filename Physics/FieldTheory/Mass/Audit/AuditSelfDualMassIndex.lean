import Physics.FieldTheory.Mass.Spectrum.Audit.AuditSelfDualMassIndex
import Physics.FieldTheory.Mass.SelfDualMassIndex
import Physics.FieldTheory.Mass.Audit.AuditAbelianMassSpectrum
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.Audit.AuditSelfDualMassIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AuditSelfDualMassIndex.circle_zero_mass_nonzero_index => Physics.AuditSelfDualMassIndex.circle_zero_mass_nonzero_index,
  GUT.AuditSelfDualMassIndex.nonzero_mass_zero_index => Physics.AuditSelfDualMassIndex.nonzero_mass_zero_index,
  GUT.AuditSelfDualMassIndex.perm3_inverse_conjugate => Physics.AuditSelfDualMassIndex.perm3_inverse_conjugate,
  GUT.AuditSelfDualMassIndex.perm3_mass_zero_index => Physics.AuditSelfDualMassIndex.perm3_mass_zero_index,
  GUT.AuditSelfDualMassIndex.signMass_nondegenerate => Physics.AuditSelfDualMassIndex.signMass_nondegenerate,
  GUT.AuditSelfDualMassIndex.signSelfDual => Physics.AuditSelfDualMassIndex.signSelfDual,
  GUT.AuditSelfDualMassIndex.zero_mass_retains_modes => Physics.AuditSelfDualMassIndex.zero_mass_retains_modes,
  GUT.AuditSelfDualMassIndex.zero_mass_zero_index => Physics.AuditSelfDualMassIndex.zero_mass_zero_index
]

assert_compatible GUT.AuditSelfDualMassIndex.circle_zero_mass_nonzero_index => Physics.AuditSelfDualMassIndex.circle_zero_mass_nonzero_index
assert_compatible GUT.AuditSelfDualMassIndex.nonzero_mass_zero_index => Physics.AuditSelfDualMassIndex.nonzero_mass_zero_index
assert_compatible GUT.AuditSelfDualMassIndex.perm3_inverse_conjugate => Physics.AuditSelfDualMassIndex.perm3_inverse_conjugate
assert_compatible GUT.AuditSelfDualMassIndex.perm3_mass_zero_index => Physics.AuditSelfDualMassIndex.perm3_mass_zero_index
assert_compatible GUT.AuditSelfDualMassIndex.signMass_nondegenerate => Physics.AuditSelfDualMassIndex.signMass_nondegenerate
assert_compatible GUT.AuditSelfDualMassIndex.signSelfDual => Physics.AuditSelfDualMassIndex.signSelfDual
assert_compatible GUT.AuditSelfDualMassIndex.zero_mass_retains_modes => Physics.AuditSelfDualMassIndex.zero_mass_retains_modes
assert_compatible GUT.AuditSelfDualMassIndex.zero_mass_zero_index => Physics.AuditSelfDualMassIndex.zero_mass_zero_index
