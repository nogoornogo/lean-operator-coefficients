import Physics.StandardModel.Gauge.Tensors.Audit.AuditExplicitSMResidualTensor
import Physics.StandardModel.Gauge.CompactExplicitSMTensor
import Math.RepresentationTheory.FiniteFlavorControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.Audit.AuditExplicitSMResidualTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExplicitSMResidualTensorAudit.a4_fields => Physics.ExplicitSMResidualTensorAudit.a4_fields,
  GUT.ExplicitSMResidualTensorAudit.matched_fields => Physics.ExplicitSMResidualTensorAudit.matched_fields,
  GUT.ExplicitSMResidualTensorAudit.s3_fields => Physics.ExplicitSMResidualTensorAudit.s3_fields
]

assert_compatible GUT.ExplicitSMResidualTensorAudit.a4_fields => Physics.ExplicitSMResidualTensorAudit.a4_fields
assert_compatible GUT.ExplicitSMResidualTensorAudit.matched_fields => Physics.ExplicitSMResidualTensorAudit.matched_fields
assert_compatible GUT.ExplicitSMResidualTensorAudit.s3_fields => Physics.ExplicitSMResidualTensorAudit.s3_fields
