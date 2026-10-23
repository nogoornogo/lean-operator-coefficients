import Physics.StandardModel.Operators.Dipole.DipolePermutationCompleteness
import Physics.StandardModel.Operators.DipoleSMCoefficient
import Math.LinearAlgebra.StatisticalCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipolePermutationCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipolePermutationCompleteness.equiv => Physics.DipolePermutationCompleteness.equiv,
  GUT.DipolePermutationCompleteness.equiv_agrees => Physics.DipolePermutationCompleteness.equiv_agrees,
  GUT.DipolePermutationCompleteness.inverse_agrees => Physics.DipolePermutationCompleteness.inverse_agrees
]

assert_compatible GUT.DipolePermutationCompleteness.equiv => Physics.DipolePermutationCompleteness.equiv
assert_compatible GUT.DipolePermutationCompleteness.equiv_agrees => Physics.DipolePermutationCompleteness.equiv_agrees
assert_compatible GUT.DipolePermutationCompleteness.inverse_agrees => Physics.DipolePermutationCompleteness.inverse_agrees
