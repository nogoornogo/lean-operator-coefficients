import Physics.StandardModel.Operators.Support.Joint.SMCombinedChargeSupport
import Physics.StandardModel.Operators.SMGenerationCauchy
import Math.RepresentationTheory.FactoredInvariantSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMCombinedChargeSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCombinedChargeSupport.action_hyper => Physics.SMCombinedChargeSupport.action_hyper,
  GUT.SMCombinedChargeSupport.allowed => Physics.SMCombinedChargeSupport.allowed,
  GUT.SMCombinedChargeSupport.decomposition => Physics.SMCombinedChargeSupport.decomposition,
  GUT.SMCombinedChargeSupport.hyper => Physics.SMCombinedChargeSupport.hyper,
  GUT.SMCombinedChargeSupport.hyper.eq_1 => Physics.SMCombinedChargeSupport.hyper.eq_1,
  GUT.SMCombinedChargeSupport.hyper_neutral => Physics.SMCombinedChargeSupport.hyper_neutral,
  GUT.SMCombinedChargeSupport.source_hyper => Physics.SMCombinedChargeSupport.source_hyper
]

assert_compatible GUT.SMCombinedChargeSupport.action_hyper => Physics.SMCombinedChargeSupport.action_hyper
assert_compatible GUT.SMCombinedChargeSupport.allowed => Physics.SMCombinedChargeSupport.allowed
assert_compatible GUT.SMCombinedChargeSupport.decomposition => Physics.SMCombinedChargeSupport.decomposition
assert_compatible GUT.SMCombinedChargeSupport.hyper => Physics.SMCombinedChargeSupport.hyper
assert_compatible GUT.SMCombinedChargeSupport.hyper.eq_1 => Physics.SMCombinedChargeSupport.hyper.eq_1
assert_compatible GUT.SMCombinedChargeSupport.hyper_neutral => Physics.SMCombinedChargeSupport.hyper_neutral
assert_compatible GUT.SMCombinedChargeSupport.source_hyper => Physics.SMCombinedChargeSupport.source_hyper
