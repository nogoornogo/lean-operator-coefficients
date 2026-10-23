import Physics.StandardModel.Operators.Support.Quark.SMQLCompactMultiplicity
import Physics.StandardModel.Operators.SMCompactMultiplicity
import Physics.StandardModel.Operators.SMQLFullKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQLCompactMultiplicity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQLCompactMultiplicity.Input => Physics.SMQLCompactMultiplicity.Input,
  GUT.SMQLCompactMultiplicity.multiplicity => Physics.SMQLCompactMultiplicity.multiplicity,
  GUT.SMQLCompactMultiplicity.original_allowed_iff => Physics.SMQLCompactMultiplicity.original_allowed_iff,
  GUT.SMQLCompactMultiplicity.original_forbidden_iff => Physics.SMQLCompactMultiplicity.original_forbidden_iff,
  GUT.SMQLCompactMultiplicity.test_allowed_iff => Physics.SMQLCompactMultiplicity.test_allowed_iff
]

assert_compatible GUT.SMQLCompactMultiplicity.Input => Physics.SMQLCompactMultiplicity.Input
assert_compatible GUT.SMQLCompactMultiplicity.multiplicity => Physics.SMQLCompactMultiplicity.multiplicity
assert_compatible GUT.SMQLCompactMultiplicity.original_allowed_iff => Physics.SMQLCompactMultiplicity.original_allowed_iff
assert_compatible GUT.SMQLCompactMultiplicity.original_forbidden_iff => Physics.SMQLCompactMultiplicity.original_forbidden_iff
assert_compatible GUT.SMQLCompactMultiplicity.test_allowed_iff => Physics.SMQLCompactMultiplicity.test_allowed_iff
