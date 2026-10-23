import Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditCompactLightQque
import Physics.StandardModel.Operators.CompactLightQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditCompactLightQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CompactLightQqueAudit.continuous_discrete_action => Physics.CompactLightQqueAudit.continuous_discrete_action,
  GUT.CompactLightQqueAudit.finite_recovery => Physics.CompactLightQqueAudit.finite_recovery
]

assert_compatible GUT.CompactLightQqueAudit.continuous_discrete_action => Physics.CompactLightQqueAudit.continuous_discrete_action
assert_compatible GUT.CompactLightQqueAudit.finite_recovery => Physics.CompactLightQqueAudit.finite_recovery
