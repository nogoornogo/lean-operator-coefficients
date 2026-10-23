import Physics.StandardModel.Spectrum.Charges.Audit.AuditIndependentProfileTotals
import Physics.StandardModel.Spectrum.FiniteChargeProfiles
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Charges.Audit.AuditIndependentProfileTotals instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FiniteChargeProfiles.AuditIndependentTotals.Residual => Physics.FiniteChargeProfiles.AuditIndependentTotals.Residual,
  GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal,
  GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal.eq_1 => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal.eq_1,
  GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal_no_common_total => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal_no_common_total,
  GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal_supported_neutral => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal_supported_neutral
]

assert_compatible GUT.FiniteChargeProfiles.AuditIndependentTotals.Residual => Physics.FiniteChargeProfiles.AuditIndependentTotals.Residual
assert_compatible GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal
assert_compatible GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal.eq_1 => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal.eq_1
assert_compatible GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal_no_common_total => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal_no_common_total
assert_compatible GUT.FiniteChargeProfiles.AuditIndependentTotals.unequal_supported_neutral => Physics.FiniteChargeProfiles.AuditIndependentTotals.unequal_supported_neutral
