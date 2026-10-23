import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenDegreeDecomposition
import Physics.StandardModel.Operators.BnvMixedInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenDegreeDecomposition instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenDegreeDecomposition.DegreeProduct => Physics.BnvSevenDegreeDecomposition.DegreeProduct,
  GUT.BnvSevenDegreeDecomposition.assemble => Physics.BnvSevenDegreeDecomposition.assemble,
  GUT.BnvSevenDegreeDecomposition.assemble.eq_1 => Physics.BnvSevenDegreeDecomposition.assemble.eq_1,
  GUT.BnvSevenDegreeDecomposition.equiv => Physics.BnvSevenDegreeDecomposition.equiv,
  GUT.BnvSevenDegreeDecomposition.outside => Physics.BnvSevenDegreeDecomposition.outside
]

assert_compatible GUT.BnvSevenDegreeDecomposition.DegreeProduct => Physics.BnvSevenDegreeDecomposition.DegreeProduct
assert_compatible GUT.BnvSevenDegreeDecomposition.assemble => Physics.BnvSevenDegreeDecomposition.assemble
assert_compatible GUT.BnvSevenDegreeDecomposition.assemble.eq_1 => Physics.BnvSevenDegreeDecomposition.assemble.eq_1
assert_compatible GUT.BnvSevenDegreeDecomposition.equiv => Physics.BnvSevenDegreeDecomposition.equiv
assert_compatible GUT.BnvSevenDegreeDecomposition.outside => Physics.BnvSevenDegreeDecomposition.outside
