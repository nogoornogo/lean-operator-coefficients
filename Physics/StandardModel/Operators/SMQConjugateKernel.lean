import Physics.StandardModel.Operators.Support.Quark.SMQConjugateKernel
import Physics.StandardModel.Operators.SMQGaussianKernel
import Physics.StandardModel.Operators.SMLConjugateMultiplicity
import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Gauge.DipoleGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQConjugateKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQConjugateKernel.actionEquiv => Physics.SMQConjugateKernel.actionEquiv,
  GUT.SMQConjugateKernel.allowed_iff => Physics.SMQConjugateKernel.allowed_iff,
  GUT.SMQConjugateKernel.coefficientEquiv => Physics.SMQConjugateKernel.coefficientEquiv,
  GUT.SMQConjugateKernel.coefficient_dimension => Physics.SMQConjugateKernel.coefficient_dimension,
  GUT.SMQConjugateKernel.fieldEquiv => Physics.SMQConjugateKernel.fieldEquiv,
  GUT.SMQConjugateKernel.kernel_dimension => Physics.SMQConjugateKernel.kernel_dimension,
  GUT.SMQConjugateKernel.rank_add_nullity => Physics.SMQConjugateKernel.rank_add_nullity,
  GUT.SMQConjugateKernel.sourceEquiv => Physics.SMQConjugateKernel.sourceEquiv
]

assert_compatible GUT.SMQConjugateKernel.actionEquiv => Physics.SMQConjugateKernel.actionEquiv
assert_compatible GUT.SMQConjugateKernel.allowed_iff => Physics.SMQConjugateKernel.allowed_iff
assert_compatible GUT.SMQConjugateKernel.coefficientEquiv => Physics.SMQConjugateKernel.coefficientEquiv
assert_compatible GUT.SMQConjugateKernel.coefficient_dimension => Physics.SMQConjugateKernel.coefficient_dimension
assert_compatible GUT.SMQConjugateKernel.fieldEquiv => Physics.SMQConjugateKernel.fieldEquiv
assert_compatible GUT.SMQConjugateKernel.kernel_dimension => Physics.SMQConjugateKernel.kernel_dimension
assert_compatible GUT.SMQConjugateKernel.rank_add_nullity => Physics.SMQConjugateKernel.rank_add_nullity
assert_compatible GUT.SMQConjugateKernel.sourceEquiv => Physics.SMQConjugateKernel.sourceEquiv
