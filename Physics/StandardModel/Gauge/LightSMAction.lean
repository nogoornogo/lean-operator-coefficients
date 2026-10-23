import Physics.StandardModel.Gauge.Tensors.LightSMAction
import Physics.StandardModel.Gauge.CompactExplicitSMTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.LightSMAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LightSMAction.Compatible => Physics.LightSMAction.Compatible,
  GUT.LightSMAction.Compatible.action => Physics.LightSMAction.Compatible.action,
  GUT.LightSMAction.Compatible.casesOn => Physics.LightSMAction.Compatible.casesOn,
  GUT.LightSMAction.Compatible.ctorIdx => Physics.LightSMAction.Compatible.ctorIdx,
  GUT.LightSMAction.Compatible.mk => Physics.LightSMAction.Compatible.mk,
  GUT.LightSMAction.Compatible.mk.inj => Physics.LightSMAction.Compatible.mk.inj,
  GUT.LightSMAction.Compatible.mk.injEq => Physics.LightSMAction.Compatible.mk.injEq,
  GUT.LightSMAction.Compatible.mk.noConfusion => Physics.LightSMAction.Compatible.mk.noConfusion,
  GUT.LightSMAction.Compatible.mk.sizeOf_spec => Physics.LightSMAction.Compatible.mk.sizeOf_spec,
  GUT.LightSMAction.Compatible.noConfusion => Physics.LightSMAction.Compatible.noConfusion,
  GUT.LightSMAction.Compatible.noConfusionType => Physics.LightSMAction.Compatible.noConfusionType,
  GUT.LightSMAction.Compatible.rec => Physics.LightSMAction.Compatible.rec,
  GUT.LightSMAction.Compatible.recOn => Physics.LightSMAction.Compatible.recOn,
  GUT.LightSMAction.Compatible.restriction => Physics.LightSMAction.Compatible.restriction,
  GUT.LightSMAction.PreservesRadical => Physics.LightSMAction.PreservesRadical,
  GUT.LightSMAction.dual_continuous => Physics.LightSMAction.dual_continuous,
  GUT.LightSMAction.dual_residual_restriction => Physics.LightSMAction.dual_residual_restriction,
  GUT.LightSMAction.dual_restriction => Physics.LightSMAction.dual_restriction,
  GUT.LightSMAction.massForAction => Physics.LightSMAction.massForAction,
  GUT.LightSMAction.massForAction_form => Physics.LightSMAction.massForAction_form,
  GUT.LightSMAction.massForAction_radical => Physics.LightSMAction.massForAction_radical,
  GUT.LightSMAction.ofDecomposition => Physics.LightSMAction.ofDecomposition,
  GUT.LightSMAction.ofInvariantMass => Physics.LightSMAction.ofInvariantMass,
  GUT.LightSMAction.ofInvariantMass_continuous => Physics.LightSMAction.ofInvariantMass_continuous,
  GUT.LightSMAction.ofPreservesRadical => Physics.LightSMAction.ofPreservesRadical,
  GUT.LightSMAction.ofPreservesRadical_apply => Physics.LightSMAction.ofPreservesRadical_apply,
  GUT.LightSMAction.ofPreservesRadical_continuous => Physics.LightSMAction.ofPreservesRadical_continuous,
  GUT.LightSMAction.preservesRadical_of_invariant => Physics.LightSMAction.preservesRadical_of_invariant,
  GUT.LightSMAction.radicalSubrepresentation => Physics.LightSMAction.radicalSubrepresentation,
  GUT.LightSMAction.residual_agrees => Physics.LightSMAction.residual_agrees,
  GUT.LightSMAction.residual_restriction => Physics.LightSMAction.residual_restriction
]

assert_compatible GUT.LightSMAction.Compatible => Physics.LightSMAction.Compatible
assert_compatible GUT.LightSMAction.Compatible.action => Physics.LightSMAction.Compatible.action
assert_compatible GUT.LightSMAction.Compatible.casesOn => Physics.LightSMAction.Compatible.casesOn
assert_compatible GUT.LightSMAction.Compatible.ctorIdx => Physics.LightSMAction.Compatible.ctorIdx
assert_compatible GUT.LightSMAction.Compatible.mk => Physics.LightSMAction.Compatible.mk
assert_compatible GUT.LightSMAction.Compatible.mk.inj => Physics.LightSMAction.Compatible.mk.inj
assert_compatible GUT.LightSMAction.Compatible.mk.injEq => Physics.LightSMAction.Compatible.mk.injEq
assert_compatible GUT.LightSMAction.Compatible.mk.noConfusion => Physics.LightSMAction.Compatible.mk.noConfusion
assert_compatible GUT.LightSMAction.Compatible.mk.sizeOf_spec => Physics.LightSMAction.Compatible.mk.sizeOf_spec
assert_compatible GUT.LightSMAction.Compatible.noConfusion => Physics.LightSMAction.Compatible.noConfusion
assert_compatible GUT.LightSMAction.Compatible.noConfusionType => Physics.LightSMAction.Compatible.noConfusionType
assert_compatible GUT.LightSMAction.Compatible.rec => Physics.LightSMAction.Compatible.rec
assert_compatible GUT.LightSMAction.Compatible.recOn => Physics.LightSMAction.Compatible.recOn
assert_compatible GUT.LightSMAction.Compatible.restriction => Physics.LightSMAction.Compatible.restriction
assert_compatible GUT.LightSMAction.PreservesRadical => Physics.LightSMAction.PreservesRadical
assert_compatible GUT.LightSMAction.dual_continuous => Physics.LightSMAction.dual_continuous
assert_compatible GUT.LightSMAction.dual_residual_restriction => Physics.LightSMAction.dual_residual_restriction
assert_compatible GUT.LightSMAction.dual_restriction => Physics.LightSMAction.dual_restriction
assert_compatible GUT.LightSMAction.massForAction => Physics.LightSMAction.massForAction
assert_compatible GUT.LightSMAction.massForAction_form => Physics.LightSMAction.massForAction_form
assert_compatible GUT.LightSMAction.massForAction_radical => Physics.LightSMAction.massForAction_radical
assert_compatible GUT.LightSMAction.ofDecomposition => Physics.LightSMAction.ofDecomposition
assert_compatible GUT.LightSMAction.ofInvariantMass => Physics.LightSMAction.ofInvariantMass
assert_compatible GUT.LightSMAction.ofInvariantMass_continuous => Physics.LightSMAction.ofInvariantMass_continuous
assert_compatible GUT.LightSMAction.ofPreservesRadical => Physics.LightSMAction.ofPreservesRadical
assert_compatible GUT.LightSMAction.ofPreservesRadical_apply => Physics.LightSMAction.ofPreservesRadical_apply
assert_compatible GUT.LightSMAction.ofPreservesRadical_continuous => Physics.LightSMAction.ofPreservesRadical_continuous
assert_compatible GUT.LightSMAction.preservesRadical_of_invariant => Physics.LightSMAction.preservesRadical_of_invariant
assert_compatible GUT.LightSMAction.radicalSubrepresentation => Physics.LightSMAction.radicalSubrepresentation
assert_compatible GUT.LightSMAction.residual_agrees => Physics.LightSMAction.residual_agrees
assert_compatible GUT.LightSMAction.residual_restriction => Physics.LightSMAction.residual_restriction
