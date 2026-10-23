import Physics.StandardModel.Gauge.Tensors.Audit.AuditLightSMAction
import Physics.StandardModel.Gauge.LightSMAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.Audit.AuditLightSMAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LightSMActionAudit.gauge => Physics.LightSMActionAudit.gauge,
  GUT.LightSMActionAudit.source => Physics.LightSMActionAudit.source,
  GUT.LightSMActionAudit.unitAction => Physics.LightSMActionAudit.unitAction,
  GUT.LightSMActionAudit.unitMass => Physics.LightSMActionAudit.unitMass,
  GUT.LightSMActionAudit.unitMass.eq_1 => Physics.LightSMActionAudit.unitMass.eq_1,
  GUT.LightSMActionAudit.unitMass_nonzero => Physics.LightSMActionAudit.unitMass_nonzero,
  GUT.LightSMActionAudit.unit_action_continuous => Physics.LightSMActionAudit.unit_action_continuous,
  GUT.LightSMActionAudit.zeroAction => Physics.LightSMActionAudit.zeroAction,
  GUT.LightSMActionAudit.zero_action_carrier => Physics.LightSMActionAudit.zero_action_carrier,
  GUT.LightSMActionAudit.zero_action_continuous => Physics.LightSMActionAudit.zero_action_continuous
]

assert_compatible GUT.LightSMActionAudit.gauge => Physics.LightSMActionAudit.gauge
assert_compatible GUT.LightSMActionAudit.source => Physics.LightSMActionAudit.source
assert_compatible GUT.LightSMActionAudit.unitAction => Physics.LightSMActionAudit.unitAction
assert_compatible GUT.LightSMActionAudit.unitMass => Physics.LightSMActionAudit.unitMass
assert_compatible GUT.LightSMActionAudit.unitMass.eq_1 => Physics.LightSMActionAudit.unitMass.eq_1
assert_compatible GUT.LightSMActionAudit.unitMass_nonzero => Physics.LightSMActionAudit.unitMass_nonzero
assert_compatible GUT.LightSMActionAudit.unit_action_continuous => Physics.LightSMActionAudit.unit_action_continuous
assert_compatible GUT.LightSMActionAudit.zeroAction => Physics.LightSMActionAudit.zeroAction
assert_compatible GUT.LightSMActionAudit.zero_action_carrier => Physics.LightSMActionAudit.zero_action_carrier
assert_compatible GUT.LightSMActionAudit.zero_action_continuous => Physics.LightSMActionAudit.zero_action_continuous
