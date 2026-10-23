import Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditFullLightSpeciesQque
import Physics.StandardModel.Operators.FullLightRadicalQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditFullLightSpeciesQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FullLightSpeciesQqueAudit.all_scalar_copies => Physics.FullLightSpeciesQqueAudit.all_scalar_copies,
  GUT.FullLightSpeciesQqueAudit.missing_up_forbidden => Physics.FullLightSpeciesQqueAudit.missing_up_forbidden
]

assert_compatible GUT.FullLightSpeciesQqueAudit.all_scalar_copies => Physics.FullLightSpeciesQqueAudit.all_scalar_copies
assert_compatible GUT.FullLightSpeciesQqueAudit.missing_up_forbidden => Physics.FullLightSpeciesQqueAudit.missing_up_forbidden
