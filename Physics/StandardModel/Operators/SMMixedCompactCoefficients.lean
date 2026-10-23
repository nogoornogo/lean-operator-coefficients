import Physics.StandardModel.Operators.Support.Joint.SMMixedCompactCoefficients
import Physics.StandardModel.Operators.SMMixedCompactWeyl
import Math.RepresentationTheory.SeparatedInvariantCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedCompactCoefficients instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMMixedCompactCoefficients.FullSpace => Physics.SMMixedCompactCoefficients.FullSpace,
  GUT.SMMixedCompactCoefficients.LocalSpace => Physics.SMMixedCompactCoefficients.LocalSpace,
  GUT.SMMixedCompactCoefficients.allowed_iff => Physics.SMMixedCompactCoefficients.allowed_iff,
  GUT.SMMixedCompactCoefficients.compactSpin => Physics.SMMixedCompactCoefficients.compactSpin,
  GUT.SMMixedCompactCoefficients.fullEquiv => Physics.SMMixedCompactCoefficients.fullEquiv,
  GUT.SMMixedCompactCoefficients.full_decomposition => Physics.SMMixedCompactCoefficients.full_decomposition,
  GUT.SMMixedCompactCoefficients.kernelEquiv => Physics.SMMixedCompactCoefficients.kernelEquiv,
  GUT.SMMixedCompactCoefficients.kernel_dimension => Physics.SMMixedCompactCoefficients.kernel_dimension,
  GUT.SMMixedCompactCoefficients.localEquiv => Physics.SMMixedCompactCoefficients.localEquiv,
  GUT.SMMixedCompactCoefficients.local_decomposition => Physics.SMMixedCompactCoefficients.local_decomposition,
  GUT.SMMixedCompactCoefficients.original_allowed_iff => Physics.SMMixedCompactCoefficients.original_allowed_iff,
  GUT.SMMixedCompactCoefficients.retained => Physics.SMMixedCompactCoefficients.retained,
  GUT.SMMixedCompactCoefficients.retained.eq_1 => Physics.SMMixedCompactCoefficients.retained.eq_1
]

assert_compatible GUT.SMMixedCompactCoefficients.FullSpace => Physics.SMMixedCompactCoefficients.FullSpace
assert_compatible GUT.SMMixedCompactCoefficients.LocalSpace => Physics.SMMixedCompactCoefficients.LocalSpace
assert_compatible GUT.SMMixedCompactCoefficients.allowed_iff => Physics.SMMixedCompactCoefficients.allowed_iff
assert_compatible GUT.SMMixedCompactCoefficients.compactSpin => Physics.SMMixedCompactCoefficients.compactSpin
assert_compatible GUT.SMMixedCompactCoefficients.fullEquiv => Physics.SMMixedCompactCoefficients.fullEquiv
assert_compatible GUT.SMMixedCompactCoefficients.full_decomposition => Physics.SMMixedCompactCoefficients.full_decomposition
assert_compatible GUT.SMMixedCompactCoefficients.kernelEquiv => Physics.SMMixedCompactCoefficients.kernelEquiv
assert_compatible GUT.SMMixedCompactCoefficients.kernel_dimension => Physics.SMMixedCompactCoefficients.kernel_dimension
assert_compatible GUT.SMMixedCompactCoefficients.localEquiv => Physics.SMMixedCompactCoefficients.localEquiv
assert_compatible GUT.SMMixedCompactCoefficients.local_decomposition => Physics.SMMixedCompactCoefficients.local_decomposition
assert_compatible GUT.SMMixedCompactCoefficients.original_allowed_iff => Physics.SMMixedCompactCoefficients.original_allowed_iff
assert_compatible GUT.SMMixedCompactCoefficients.retained => Physics.SMMixedCompactCoefficients.retained
assert_compatible GUT.SMMixedCompactCoefficients.retained.eq_1 => Physics.SMMixedCompactCoefficients.retained.eq_1
