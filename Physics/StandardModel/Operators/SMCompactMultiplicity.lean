import Physics.StandardModel.Operators.Support.Decomposition.SMCompactMultiplicity
import Physics.StandardModel.Operators.SMCompactTorus
import Physics.StandardModel.Operators.SMWeylExtractionInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMCompactMultiplicity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCompactMultiplicity.Input => Physics.SMCompactMultiplicity.Input,
  GUT.SMCompactMultiplicity.compactBorel => Physics.SMCompactMultiplicity.compactBorel,
  GUT.SMCompactMultiplicity.compactMeasurable => Physics.SMCompactMultiplicity.compactMeasurable,
  GUT.SMCompactMultiplicity.kernel_dimension => Physics.SMCompactMultiplicity.kernel_dimension,
  GUT.SMCompactMultiplicity.kernel_dimension_int => Physics.SMCompactMultiplicity.kernel_dimension_int,
  GUT.SMCompactMultiplicity.local_allowed_iff => Physics.SMCompactMultiplicity.local_allowed_iff,
  GUT.SMCompactMultiplicity.model => Physics.SMCompactMultiplicity.model,
  GUT.SMCompactMultiplicity.multiplicity => Physics.SMCompactMultiplicity.multiplicity,
  GUT.SMCompactMultiplicity.nonnegative => Physics.SMCompactMultiplicity.nonnegative,
  GUT.SMCompactMultiplicity.polynomial => Physics.SMCompactMultiplicity.polynomial,
  GUT.SMCompactMultiplicity.presents => Physics.SMCompactMultiplicity.presents,
  GUT.SMCompactMultiplicity.rank_formula => Physics.SMCompactMultiplicity.rank_formula
]

assert_compatible GUT.SMCompactMultiplicity.Input => Physics.SMCompactMultiplicity.Input
assert_compatible GUT.SMCompactMultiplicity.compactBorel => Physics.SMCompactMultiplicity.compactBorel
assert_compatible GUT.SMCompactMultiplicity.compactMeasurable => Physics.SMCompactMultiplicity.compactMeasurable
assert_compatible GUT.SMCompactMultiplicity.kernel_dimension => Physics.SMCompactMultiplicity.kernel_dimension
assert_compatible GUT.SMCompactMultiplicity.kernel_dimension_int => Physics.SMCompactMultiplicity.kernel_dimension_int
assert_compatible GUT.SMCompactMultiplicity.local_allowed_iff => Physics.SMCompactMultiplicity.local_allowed_iff
assert_compatible GUT.SMCompactMultiplicity.model => Physics.SMCompactMultiplicity.model
assert_compatible GUT.SMCompactMultiplicity.multiplicity => Physics.SMCompactMultiplicity.multiplicity
assert_compatible GUT.SMCompactMultiplicity.nonnegative => Physics.SMCompactMultiplicity.nonnegative
assert_compatible GUT.SMCompactMultiplicity.polynomial => Physics.SMCompactMultiplicity.polynomial
assert_compatible GUT.SMCompactMultiplicity.presents => Physics.SMCompactMultiplicity.presents
assert_compatible GUT.SMCompactMultiplicity.rank_formula => Physics.SMCompactMultiplicity.rank_formula
