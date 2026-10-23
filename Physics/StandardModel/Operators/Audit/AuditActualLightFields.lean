import Physics.StandardModel.Operators.Selection.Audit.AuditActualLightFields
import Physics.StandardModel.Operators.LightSMSpeciesQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.Audit.AuditActualLightFields instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ActualLightFieldsAudit.actual_subspaces => Physics.ActualLightFieldsAudit.actual_subspaces,
  GUT.ActualLightFieldsAudit.ambient => Physics.ActualLightFieldsAudit.ambient,
  GUT.ActualLightFieldsAudit.emptyExtra => Physics.ActualLightFieldsAudit.emptyExtra,
  GUT.ActualLightFieldsAudit.extraSelfDual => Physics.ActualLightFieldsAudit.extraSelfDual,
  GUT.ActualLightFieldsAudit.flavor => Physics.ActualLightFieldsAudit.flavor,
  GUT.ActualLightFieldsAudit.instAddCommGroupQuark => Physics.ActualLightFieldsAudit.instAddCommGroupQuark,
  GUT.ActualLightFieldsAudit.instAddCommGroupTensorProductComplexQuark => Physics.ActualLightFieldsAudit.instAddCommGroupTensorProductComplexQuark,
  GUT.ActualLightFieldsAudit.leftE => Physics.ActualLightFieldsAudit.leftE,
  GUT.ActualLightFieldsAudit.leftQ => Physics.ActualLightFieldsAudit.leftQ,
  GUT.ActualLightFieldsAudit.leftU => Physics.ActualLightFieldsAudit.leftU,
  GUT.ActualLightFieldsAudit.one_generation => Physics.ActualLightFieldsAudit.one_generation,
  GUT.ActualLightFieldsAudit.selfDualExtra => Physics.ActualLightFieldsAudit.selfDualExtra,
  GUT.ActualLightFieldsAudit.singlet => Physics.ActualLightFieldsAudit.singlet,
  GUT.ActualLightFieldsAudit.with_self_dual_extra => Physics.ActualLightFieldsAudit.with_self_dual_extra
]

assert_compatible GUT.ActualLightFieldsAudit.actual_subspaces => Physics.ActualLightFieldsAudit.actual_subspaces
assert_compatible GUT.ActualLightFieldsAudit.ambient => Physics.ActualLightFieldsAudit.ambient
assert_compatible GUT.ActualLightFieldsAudit.emptyExtra => Physics.ActualLightFieldsAudit.emptyExtra
assert_compatible GUT.ActualLightFieldsAudit.extraSelfDual => Physics.ActualLightFieldsAudit.extraSelfDual
assert_compatible GUT.ActualLightFieldsAudit.flavor => Physics.ActualLightFieldsAudit.flavor
assert_compatible GUT.ActualLightFieldsAudit.instAddCommGroupQuark => Physics.ActualLightFieldsAudit.instAddCommGroupQuark
assert_compatible GUT.ActualLightFieldsAudit.instAddCommGroupTensorProductComplexQuark => Physics.ActualLightFieldsAudit.instAddCommGroupTensorProductComplexQuark
assert_compatible GUT.ActualLightFieldsAudit.leftE => Physics.ActualLightFieldsAudit.leftE
assert_compatible GUT.ActualLightFieldsAudit.leftQ => Physics.ActualLightFieldsAudit.leftQ
assert_compatible GUT.ActualLightFieldsAudit.leftU => Physics.ActualLightFieldsAudit.leftU
assert_compatible GUT.ActualLightFieldsAudit.one_generation => Physics.ActualLightFieldsAudit.one_generation
assert_compatible GUT.ActualLightFieldsAudit.selfDualExtra => Physics.ActualLightFieldsAudit.selfDualExtra
assert_compatible GUT.ActualLightFieldsAudit.singlet => Physics.ActualLightFieldsAudit.singlet
assert_compatible GUT.ActualLightFieldsAudit.with_self_dual_extra => Physics.ActualLightFieldsAudit.with_self_dual_extra
