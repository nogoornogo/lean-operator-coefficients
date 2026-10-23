import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenCompleteness
import Physics.StandardModel.Operators.BnvSixResidualCompleteness
import Physics.StandardModel.Operators.BnvSevenSignedCoordinates
import Physics.StandardModel.Operators.BnvSevenDegreeDecomposition
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenCompleteness.ResidualProduct => Physics.BnvSevenCompleteness.ResidualProduct,
  GUT.BnvSevenCompleteness.equiv => Physics.BnvSevenCompleteness.equiv,
  GUT.BnvSevenCompleteness.extract => Physics.BnvSevenCompleteness.extract,
  GUT.BnvSevenCompleteness.extract_reconstruct => Physics.BnvSevenCompleteness.extract_reconstruct,
  GUT.BnvSevenCompleteness.forbidden_iff => Physics.BnvSevenCompleteness.forbidden_iff,
  GUT.BnvSevenCompleteness.nonzero_iff => Physics.BnvSevenCompleteness.nonzero_iff,
  GUT.BnvSevenCompleteness.reconstruct => Physics.BnvSevenCompleteness.reconstruct,
  GUT.BnvSevenCompleteness.reconstruct_extract => Physics.BnvSevenCompleteness.reconstruct_extract
]

assert_compatible GUT.BnvSevenCompleteness.ResidualProduct => Physics.BnvSevenCompleteness.ResidualProduct
assert_compatible GUT.BnvSevenCompleteness.equiv => Physics.BnvSevenCompleteness.equiv
assert_compatible GUT.BnvSevenCompleteness.extract => Physics.BnvSevenCompleteness.extract
assert_compatible GUT.BnvSevenCompleteness.extract_reconstruct => Physics.BnvSevenCompleteness.extract_reconstruct
assert_compatible GUT.BnvSevenCompleteness.forbidden_iff => Physics.BnvSevenCompleteness.forbidden_iff
assert_compatible GUT.BnvSevenCompleteness.nonzero_iff => Physics.BnvSevenCompleteness.nonzero_iff
assert_compatible GUT.BnvSevenCompleteness.reconstruct => Physics.BnvSevenCompleteness.reconstruct
assert_compatible GUT.BnvSevenCompleteness.reconstruct_extract => Physics.BnvSevenCompleteness.reconstruct_extract
