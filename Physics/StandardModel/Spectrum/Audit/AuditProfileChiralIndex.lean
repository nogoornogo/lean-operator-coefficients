import Physics.StandardModel.Spectrum.Charges.Audit.AuditProfileChiralIndex
import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Physics.StandardModel.Spectrum.Audit.AuditFiniteChargeProfiles
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Charges.Audit.AuditProfileChiralIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AuditFiniteChargeProfiles.cyclicLabels.congr_simp => Physics.AuditFiniteChargeProfiles.cyclicLabels.congr_simp,
  GUT.AuditProfileChiralIndex.Label => Physics.AuditProfileChiralIndex.Label,
  GUT.AuditProfileChiralIndex.torsion_singlet_invisible => Physics.AuditProfileChiralIndex.torsion_singlet_invisible,
  GUT.AuditProfileChiralIndex.torsion_target_coefficient => Physics.AuditProfileChiralIndex.torsion_target_coefficient,
  GUT.AuditProfileChiralIndex.vectorlike_pairs_preserve_target => Physics.AuditProfileChiralIndex.vectorlike_pairs_preserve_target,
  GUT.AuditProfileChiralIndex.wrong_orientation_control => Physics.AuditProfileChiralIndex.wrong_orientation_control
]

assert_compatible GUT.AuditFiniteChargeProfiles.cyclicLabels.congr_simp => Physics.AuditFiniteChargeProfiles.cyclicLabels.congr_simp
assert_compatible GUT.AuditProfileChiralIndex.Label => Physics.AuditProfileChiralIndex.Label
assert_compatible GUT.AuditProfileChiralIndex.torsion_singlet_invisible => Physics.AuditProfileChiralIndex.torsion_singlet_invisible
assert_compatible GUT.AuditProfileChiralIndex.torsion_target_coefficient => Physics.AuditProfileChiralIndex.torsion_target_coefficient
assert_compatible GUT.AuditProfileChiralIndex.vectorlike_pairs_preserve_target => Physics.AuditProfileChiralIndex.vectorlike_pairs_preserve_target
assert_compatible GUT.AuditProfileChiralIndex.wrong_orientation_control => Physics.AuditProfileChiralIndex.wrong_orientation_control
