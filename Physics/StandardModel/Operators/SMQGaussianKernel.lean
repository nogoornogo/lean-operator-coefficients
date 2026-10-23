import Physics.StandardModel.Operators.Support.Quark.SMQGaussianKernel
import Physics.StandardModel.Operators.SMQExactCoordinates
import Math.LinearAlgebra.GramNullityPolynomial
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQGaussianKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQGaussianKernel.allowed_iff => Physics.SMQGaussianKernel.allowed_iff,
  GUT.SMQGaussianKernel.carrierFinite => Physics.SMQGaussianKernel.carrierFinite,
  GUT.SMQGaussianKernel.coefficient_dimension => Physics.SMQGaussianKernel.coefficient_dimension,
  GUT.SMQGaussianKernel.forbidden_charged => Physics.SMQGaussianKernel.forbidden_charged,
  GUT.SMQGaussianKernel.forbidden_odd => Physics.SMQGaussianKernel.forbidden_odd,
  GUT.SMQGaussianKernel.kernel_dimension => Physics.SMQGaussianKernel.kernel_dimension,
  GUT.SMQGaussianKernel.matrix => Physics.SMQGaussianKernel.matrix,
  GUT.SMQGaussianKernel.matrix.eq_1 => Physics.SMQGaussianKernel.matrix.eq_1,
  GUT.SMQGaussianKernel.matrix_semantics => Physics.SMQGaussianKernel.matrix_semantics,
  GUT.SMQGaussianKernel.nullity_above_capacity => Physics.SMQGaussianKernel.nullity_above_capacity,
  GUT.SMQGaussianKernel.polynomial => Physics.SMQGaussianKernel.polynomial,
  GUT.SMQGaussianKernel.rank_add_nullity => Physics.SMQGaussianKernel.rank_add_nullity
]

assert_compatible GUT.SMQGaussianKernel.allowed_iff => Physics.SMQGaussianKernel.allowed_iff
assert_compatible GUT.SMQGaussianKernel.carrierFinite => Physics.SMQGaussianKernel.carrierFinite
assert_compatible GUT.SMQGaussianKernel.coefficient_dimension => Physics.SMQGaussianKernel.coefficient_dimension
assert_compatible GUT.SMQGaussianKernel.forbidden_charged => Physics.SMQGaussianKernel.forbidden_charged
assert_compatible GUT.SMQGaussianKernel.forbidden_odd => Physics.SMQGaussianKernel.forbidden_odd
assert_compatible GUT.SMQGaussianKernel.kernel_dimension => Physics.SMQGaussianKernel.kernel_dimension
assert_compatible GUT.SMQGaussianKernel.matrix => Physics.SMQGaussianKernel.matrix
assert_compatible GUT.SMQGaussianKernel.matrix.eq_1 => Physics.SMQGaussianKernel.matrix.eq_1
assert_compatible GUT.SMQGaussianKernel.matrix_semantics => Physics.SMQGaussianKernel.matrix_semantics
assert_compatible GUT.SMQGaussianKernel.nullity_above_capacity => Physics.SMQGaussianKernel.nullity_above_capacity
assert_compatible GUT.SMQGaussianKernel.polynomial => Physics.SMQGaussianKernel.polynomial
assert_compatible GUT.SMQGaussianKernel.rank_add_nullity => Physics.SMQGaussianKernel.rank_add_nullity
