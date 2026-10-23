import Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditCompactLightExteriorQque
import Physics.StandardModel.Operators.CompactLightExteriorQque
import Math.RepresentationTheory.FiniteFlavorControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.Audit.AuditCompactLightExteriorQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CompactLightExteriorQqueAudit.a4_fields => Physics.CompactLightExteriorQqueAudit.a4_fields,
  GUT.CompactLightExteriorQqueAudit.identitySplit => Physics.CompactLightExteriorQqueAudit.identitySplit,
  GUT.CompactLightExteriorQqueAudit.one_generation => Physics.CompactLightExteriorQqueAudit.one_generation,
  GUT.CompactLightExteriorQqueAudit.s3_fields => Physics.CompactLightExteriorQqueAudit.s3_fields
]

assert_compatible GUT.CompactLightExteriorQqueAudit.a4_fields => Physics.CompactLightExteriorQqueAudit.a4_fields
assert_compatible GUT.CompactLightExteriorQqueAudit.identitySplit => Physics.CompactLightExteriorQqueAudit.identitySplit
assert_compatible GUT.CompactLightExteriorQqueAudit.one_generation => Physics.CompactLightExteriorQqueAudit.one_generation
assert_compatible GUT.CompactLightExteriorQqueAudit.s3_fields => Physics.CompactLightExteriorQqueAudit.s3_fields
