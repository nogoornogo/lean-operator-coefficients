import Physics.StandardModel.Operators.Support.Decomposition.SMCompactSupportExamples
import Physics.StandardModel.Operators.SMCompactSupportDecision
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMCompactSupportExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCompactSupportExamples.mixedForbidden => Physics.SMCompactSupportExamples.mixedForbidden,
  GUT.SMCompactSupportExamples.q18Allowed => Physics.SMCompactSupportExamples.q18Allowed
]

assert_compatible GUT.SMCompactSupportExamples.mixedForbidden => Physics.SMCompactSupportExamples.mixedForbidden
assert_compatible GUT.SMCompactSupportExamples.q18Allowed => Physics.SMCompactSupportExamples.q18Allowed
