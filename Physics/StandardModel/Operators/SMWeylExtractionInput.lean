import Physics.StandardModel.Operators.Support.Coordinates.SMWeylExtractionInput
import Physics.StandardModel.Operators.SMIteratedContent
import Physics.StandardModel.Operators.SMMixedCompactCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMWeylExtractionInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMWeylExtractionInput.kernel_dimension => Physics.SMWeylExtractionInput.kernel_dimension,
  GUT.SMWeylExtractionInput.kernel_dimension_int => Physics.SMWeylExtractionInput.kernel_dimension_int,
  GUT.SMWeylExtractionInput.local_allowed_iff => Physics.SMWeylExtractionInput.local_allowed_iff,
  GUT.SMWeylExtractionInput.multiplicity_le_columns => Physics.SMWeylExtractionInput.multiplicity_le_columns,
  GUT.SMWeylExtractionInput.multiplicity_nonnegative => Physics.SMWeylExtractionInput.multiplicity_nonnegative,
  GUT.SMWeylExtractionInput.rank_formula => Physics.SMWeylExtractionInput.rank_formula
]

assert_compatible GUT.SMWeylExtractionInput.kernel_dimension => Physics.SMWeylExtractionInput.kernel_dimension
assert_compatible GUT.SMWeylExtractionInput.kernel_dimension_int => Physics.SMWeylExtractionInput.kernel_dimension_int
assert_compatible GUT.SMWeylExtractionInput.local_allowed_iff => Physics.SMWeylExtractionInput.local_allowed_iff
assert_compatible GUT.SMWeylExtractionInput.multiplicity_le_columns => Physics.SMWeylExtractionInput.multiplicity_le_columns
assert_compatible GUT.SMWeylExtractionInput.multiplicity_nonnegative => Physics.SMWeylExtractionInput.multiplicity_nonnegative
assert_compatible GUT.SMWeylExtractionInput.rank_formula => Physics.SMWeylExtractionInput.rank_formula
