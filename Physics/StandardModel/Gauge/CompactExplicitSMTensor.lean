import Physics.StandardModel.Gauge.Tensors.CompactExplicitSMTensor
import Physics.StandardModel.Gauge.ExplicitSMResidualTensor
import Physics.StandardModel.Gauge.PhysicalTorus
import Physics.StandardModel.Operators.CompactLightQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.CompactExplicitSMTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CompactExplicitSMTensor.Decomposition => Physics.CompactExplicitSMTensor.Decomposition,
  GUT.CompactExplicitSMTensor.Decomposition.action => Physics.CompactExplicitSMTensor.Decomposition.action,
  GUT.CompactExplicitSMTensor.Decomposition.casesOn => Physics.CompactExplicitSMTensor.Decomposition.casesOn,
  GUT.CompactExplicitSMTensor.Decomposition.ctorIdx => Physics.CompactExplicitSMTensor.Decomposition.ctorIdx,
  GUT.CompactExplicitSMTensor.Decomposition.electron14 => Physics.CompactExplicitSMTensor.Decomposition.electron14,
  GUT.CompactExplicitSMTensor.Decomposition.electronRight => Physics.CompactExplicitSMTensor.Decomposition.electronRight,
  GUT.CompactExplicitSMTensor.Decomposition.mk => Physics.CompactExplicitSMTensor.Decomposition.mk,
  GUT.CompactExplicitSMTensor.Decomposition.mk.inj => Physics.CompactExplicitSMTensor.Decomposition.mk.inj,
  GUT.CompactExplicitSMTensor.Decomposition.mk.injEq => Physics.CompactExplicitSMTensor.Decomposition.mk.injEq,
  GUT.CompactExplicitSMTensor.Decomposition.mk.noConfusion => Physics.CompactExplicitSMTensor.Decomposition.mk.noConfusion,
  GUT.CompactExplicitSMTensor.Decomposition.mk.sizeOf_spec => Physics.CompactExplicitSMTensor.Decomposition.mk.sizeOf_spec,
  GUT.CompactExplicitSMTensor.Decomposition.noConfusion => Physics.CompactExplicitSMTensor.Decomposition.noConfusion,
  GUT.CompactExplicitSMTensor.Decomposition.noConfusionType => Physics.CompactExplicitSMTensor.Decomposition.noConfusionType,
  GUT.CompactExplicitSMTensor.Decomposition.quark => Physics.CompactExplicitSMTensor.Decomposition.quark,
  GUT.CompactExplicitSMTensor.Decomposition.quark0 => Physics.CompactExplicitSMTensor.Decomposition.quark0,
  GUT.CompactExplicitSMTensor.Decomposition.quark3 => Physics.CompactExplicitSMTensor.Decomposition.quark3,
  GUT.CompactExplicitSMTensor.Decomposition.rec => Physics.CompactExplicitSMTensor.Decomposition.rec,
  GUT.CompactExplicitSMTensor.Decomposition.recOn => Physics.CompactExplicitSMTensor.Decomposition.recOn,
  GUT.CompactExplicitSMTensor.Decomposition.restriction => Physics.CompactExplicitSMTensor.Decomposition.restriction,
  GUT.CompactExplicitSMTensor.Decomposition.up8 => Physics.CompactExplicitSMTensor.Decomposition.up8,
  GUT.CompactExplicitSMTensor.Decomposition.upRight => Physics.CompactExplicitSMTensor.Decomposition.upRight,
  GUT.CompactExplicitSMTensor.exists_qque => Physics.CompactExplicitSMTensor.exists_qque,
  GUT.CompactExplicitSMTensor.fieldTensor => Physics.CompactExplicitSMTensor.fieldTensor,
  GUT.CompactExplicitSMTensor.residual_agrees => Physics.CompactExplicitSMTensor.residual_agrees
]

assert_compatible GUT.CompactExplicitSMTensor.Decomposition => Physics.CompactExplicitSMTensor.Decomposition
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.action => Physics.CompactExplicitSMTensor.Decomposition.action
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.casesOn => Physics.CompactExplicitSMTensor.Decomposition.casesOn
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.ctorIdx => Physics.CompactExplicitSMTensor.Decomposition.ctorIdx
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.electron14 => Physics.CompactExplicitSMTensor.Decomposition.electron14
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.electronRight => Physics.CompactExplicitSMTensor.Decomposition.electronRight
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.mk => Physics.CompactExplicitSMTensor.Decomposition.mk
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.mk.inj => Physics.CompactExplicitSMTensor.Decomposition.mk.inj
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.mk.injEq => Physics.CompactExplicitSMTensor.Decomposition.mk.injEq
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.mk.noConfusion => Physics.CompactExplicitSMTensor.Decomposition.mk.noConfusion
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.mk.sizeOf_spec => Physics.CompactExplicitSMTensor.Decomposition.mk.sizeOf_spec
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.noConfusion => Physics.CompactExplicitSMTensor.Decomposition.noConfusion
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.noConfusionType => Physics.CompactExplicitSMTensor.Decomposition.noConfusionType
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.quark => Physics.CompactExplicitSMTensor.Decomposition.quark
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.quark0 => Physics.CompactExplicitSMTensor.Decomposition.quark0
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.quark3 => Physics.CompactExplicitSMTensor.Decomposition.quark3
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.rec => Physics.CompactExplicitSMTensor.Decomposition.rec
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.recOn => Physics.CompactExplicitSMTensor.Decomposition.recOn
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.restriction => Physics.CompactExplicitSMTensor.Decomposition.restriction
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.up8 => Physics.CompactExplicitSMTensor.Decomposition.up8
assert_compatible GUT.CompactExplicitSMTensor.Decomposition.upRight => Physics.CompactExplicitSMTensor.Decomposition.upRight
assert_compatible GUT.CompactExplicitSMTensor.exists_qque => Physics.CompactExplicitSMTensor.exists_qque
assert_compatible GUT.CompactExplicitSMTensor.fieldTensor => Physics.CompactExplicitSMTensor.fieldTensor
assert_compatible GUT.CompactExplicitSMTensor.residual_agrees => Physics.CompactExplicitSMTensor.residual_agrees
