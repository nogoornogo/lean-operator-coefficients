import Physics.StandardModel.Spectrum.Representations.Audit.AuditPartialTargetExtras
import Physics.StandardModel.Spectrum.SMPartialTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.Audit.AuditPartialTargetExtras instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMPartialTarget.AuditExtras.Charge => Physics.SMPartialTarget.AuditExtras.Charge,
  GUT.SMPartialTarget.AuditExtras.contaminant => Physics.SMPartialTarget.AuditExtras.contaminant,
  GUT.SMPartialTarget.AuditExtras.contaminant.eq_1 => Physics.SMPartialTarget.AuditExtras.contaminant.eq_1,
  GUT.SMPartialTarget.AuditExtras.contaminant_breaks_matching => Physics.SMPartialTarget.AuditExtras.contaminant_breaks_matching,
  GUT.SMPartialTarget.AuditExtras.contaminant_vanishes_at_positive_sm => Physics.SMPartialTarget.AuditExtras.contaminant_vanishes_at_positive_sm,
  GUT.SMPartialTarget.AuditExtras.exotic => Physics.SMPartialTarget.AuditExtras.exotic,
  GUT.SMPartialTarget.AuditExtras.exotic_ne_neg => Physics.SMPartialTarget.AuditExtras.exotic_ne_neg,
  GUT.SMPartialTarget.AuditExtras.exotic_ne_neg_sm => Physics.SMPartialTarget.AuditExtras.exotic_ne_neg_sm,
  GUT.SMPartialTarget.AuditExtras.exotic_ne_sm => Physics.SMPartialTarget.AuditExtras.exotic_ne_sm,
  GUT.SMPartialTarget.AuditExtras.exotic_nonzero => Physics.SMPartialTarget.AuditExtras.exotic_nonzero,
  GUT.SMPartialTarget.AuditExtras.extra => Physics.SMPartialTarget.AuditExtras.extra,
  GUT.SMPartialTarget.AuditExtras.extra.eq_1 => Physics.SMPartialTarget.AuditExtras.extra.eq_1,
  GUT.SMPartialTarget.AuditExtras.extra_dual_nonzero => Physics.SMPartialTarget.AuditExtras.extra_dual_nonzero,
  GUT.SMPartialTarget.AuditExtras.extra_dual_vanishes => Physics.SMPartialTarget.AuditExtras.extra_dual_vanishes,
  GUT.SMPartialTarget.AuditExtras.neg_exotic_ne_sm => Physics.SMPartialTarget.AuditExtras.neg_exotic_ne_sm,
  GUT.SMPartialTarget.AuditExtras.with_extra_matches => Physics.SMPartialTarget.AuditExtras.with_extra_matches,
  GUT.SMPartialTarget.AuditExtras.with_extra_not_full_target => Physics.SMPartialTarget.AuditExtras.with_extra_not_full_target
]

assert_compatible GUT.SMPartialTarget.AuditExtras.Charge => Physics.SMPartialTarget.AuditExtras.Charge
assert_compatible GUT.SMPartialTarget.AuditExtras.contaminant => Physics.SMPartialTarget.AuditExtras.contaminant
assert_compatible GUT.SMPartialTarget.AuditExtras.contaminant.eq_1 => Physics.SMPartialTarget.AuditExtras.contaminant.eq_1
assert_compatible GUT.SMPartialTarget.AuditExtras.contaminant_breaks_matching => Physics.SMPartialTarget.AuditExtras.contaminant_breaks_matching
assert_compatible GUT.SMPartialTarget.AuditExtras.contaminant_vanishes_at_positive_sm => Physics.SMPartialTarget.AuditExtras.contaminant_vanishes_at_positive_sm
assert_compatible GUT.SMPartialTarget.AuditExtras.exotic => Physics.SMPartialTarget.AuditExtras.exotic
assert_compatible GUT.SMPartialTarget.AuditExtras.exotic_ne_neg => Physics.SMPartialTarget.AuditExtras.exotic_ne_neg
assert_compatible GUT.SMPartialTarget.AuditExtras.exotic_ne_neg_sm => Physics.SMPartialTarget.AuditExtras.exotic_ne_neg_sm
assert_compatible GUT.SMPartialTarget.AuditExtras.exotic_ne_sm => Physics.SMPartialTarget.AuditExtras.exotic_ne_sm
assert_compatible GUT.SMPartialTarget.AuditExtras.exotic_nonzero => Physics.SMPartialTarget.AuditExtras.exotic_nonzero
assert_compatible GUT.SMPartialTarget.AuditExtras.extra => Physics.SMPartialTarget.AuditExtras.extra
assert_compatible GUT.SMPartialTarget.AuditExtras.extra.eq_1 => Physics.SMPartialTarget.AuditExtras.extra.eq_1
assert_compatible GUT.SMPartialTarget.AuditExtras.extra_dual_nonzero => Physics.SMPartialTarget.AuditExtras.extra_dual_nonzero
assert_compatible GUT.SMPartialTarget.AuditExtras.extra_dual_vanishes => Physics.SMPartialTarget.AuditExtras.extra_dual_vanishes
assert_compatible GUT.SMPartialTarget.AuditExtras.neg_exotic_ne_sm => Physics.SMPartialTarget.AuditExtras.neg_exotic_ne_sm
assert_compatible GUT.SMPartialTarget.AuditExtras.with_extra_matches => Physics.SMPartialTarget.AuditExtras.with_extra_matches
assert_compatible GUT.SMPartialTarget.AuditExtras.with_extra_not_full_target => Physics.SMPartialTarget.AuditExtras.with_extra_not_full_target
