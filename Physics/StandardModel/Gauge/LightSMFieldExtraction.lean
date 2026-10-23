import Physics.StandardModel.Gauge.Tensors.LightSMFieldExtraction
import Physics.StandardModel.Gauge.StandardSMIrreducibility
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.LightSMFieldExtraction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LightSMFieldExtraction.Fields => Physics.LightSMFieldExtraction.Fields,
  GUT.LightSMFieldExtraction.Fields.E => Physics.LightSMFieldExtraction.Fields.E,
  GUT.LightSMFieldExtraction.Fields.Q => Physics.LightSMFieldExtraction.Fields.Q,
  GUT.LightSMFieldExtraction.Fields.U => Physics.LightSMFieldExtraction.Fields.U,
  GUT.LightSMFieldExtraction.Fields.casesOn => Physics.LightSMFieldExtraction.Fields.casesOn,
  GUT.LightSMFieldExtraction.Fields.ctorIdx => Physics.LightSMFieldExtraction.Fields.ctorIdx,
  GUT.LightSMFieldExtraction.Fields.electronEquiv => Physics.LightSMFieldExtraction.Fields.electronEquiv,
  GUT.LightSMFieldExtraction.Fields.mk => Physics.LightSMFieldExtraction.Fields.mk,
  GUT.LightSMFieldExtraction.Fields.mk.inj => Physics.LightSMFieldExtraction.Fields.mk.inj,
  GUT.LightSMFieldExtraction.Fields.mk.injEq => Physics.LightSMFieldExtraction.Fields.mk.injEq,
  GUT.LightSMFieldExtraction.Fields.mk.noConfusion => Physics.LightSMFieldExtraction.Fields.mk.noConfusion,
  GUT.LightSMFieldExtraction.Fields.mk.sizeOf_spec => Physics.LightSMFieldExtraction.Fields.mk.sizeOf_spec,
  GUT.LightSMFieldExtraction.Fields.noConfusion => Physics.LightSMFieldExtraction.Fields.noConfusion,
  GUT.LightSMFieldExtraction.Fields.noConfusionType => Physics.LightSMFieldExtraction.Fields.noConfusionType,
  GUT.LightSMFieldExtraction.Fields.quarkEquiv => Physics.LightSMFieldExtraction.Fields.quarkEquiv,
  GUT.LightSMFieldExtraction.Fields.rec => Physics.LightSMFieldExtraction.Fields.rec,
  GUT.LightSMFieldExtraction.Fields.recOn => Physics.LightSMFieldExtraction.Fields.recOn,
  GUT.LightSMFieldExtraction.Fields.upEquiv => Physics.LightSMFieldExtraction.Fields.upEquiv,
  GUT.LightSMFieldExtraction.nonempty_fields => Physics.LightSMFieldExtraction.nonempty_fields
]

assert_compatible GUT.LightSMFieldExtraction.Fields => Physics.LightSMFieldExtraction.Fields
assert_compatible GUT.LightSMFieldExtraction.Fields.E => Physics.LightSMFieldExtraction.Fields.E
assert_compatible GUT.LightSMFieldExtraction.Fields.Q => Physics.LightSMFieldExtraction.Fields.Q
assert_compatible GUT.LightSMFieldExtraction.Fields.U => Physics.LightSMFieldExtraction.Fields.U
assert_compatible GUT.LightSMFieldExtraction.Fields.casesOn => Physics.LightSMFieldExtraction.Fields.casesOn
assert_compatible GUT.LightSMFieldExtraction.Fields.ctorIdx => Physics.LightSMFieldExtraction.Fields.ctorIdx
assert_compatible GUT.LightSMFieldExtraction.Fields.electronEquiv => Physics.LightSMFieldExtraction.Fields.electronEquiv
assert_compatible GUT.LightSMFieldExtraction.Fields.mk => Physics.LightSMFieldExtraction.Fields.mk
assert_compatible GUT.LightSMFieldExtraction.Fields.mk.inj => Physics.LightSMFieldExtraction.Fields.mk.inj
assert_compatible GUT.LightSMFieldExtraction.Fields.mk.injEq => Physics.LightSMFieldExtraction.Fields.mk.injEq
assert_compatible GUT.LightSMFieldExtraction.Fields.mk.noConfusion => Physics.LightSMFieldExtraction.Fields.mk.noConfusion
assert_compatible GUT.LightSMFieldExtraction.Fields.mk.sizeOf_spec => Physics.LightSMFieldExtraction.Fields.mk.sizeOf_spec
assert_compatible GUT.LightSMFieldExtraction.Fields.noConfusion => Physics.LightSMFieldExtraction.Fields.noConfusion
assert_compatible GUT.LightSMFieldExtraction.Fields.noConfusionType => Physics.LightSMFieldExtraction.Fields.noConfusionType
assert_compatible GUT.LightSMFieldExtraction.Fields.quarkEquiv => Physics.LightSMFieldExtraction.Fields.quarkEquiv
assert_compatible GUT.LightSMFieldExtraction.Fields.rec => Physics.LightSMFieldExtraction.Fields.rec
assert_compatible GUT.LightSMFieldExtraction.Fields.recOn => Physics.LightSMFieldExtraction.Fields.recOn
assert_compatible GUT.LightSMFieldExtraction.Fields.upEquiv => Physics.LightSMFieldExtraction.Fields.upEquiv
assert_compatible GUT.LightSMFieldExtraction.nonempty_fields => Physics.LightSMFieldExtraction.nonempty_fields
