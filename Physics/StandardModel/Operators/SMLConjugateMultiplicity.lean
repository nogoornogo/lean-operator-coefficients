import Physics.StandardModel.Operators.Support.Lepton.SMLConjugateMultiplicity
import Physics.StandardModel.Operators.SMLKernelDimension
import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Gauge.DipoleGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Lepton.SMLConjugateMultiplicity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMLConjugateMultiplicity.actionEquiv => Physics.SMLConjugateMultiplicity.actionEquiv,
  GUT.SMLConjugateMultiplicity.allowed_iff => Physics.SMLConjugateMultiplicity.allowed_iff,
  GUT.SMLConjugateMultiplicity.bosonEquiv => Physics.SMLConjugateMultiplicity.bosonEquiv,
  GUT.SMLConjugateMultiplicity.coefficientEquiv => Physics.SMLConjugateMultiplicity.coefficientEquiv,
  GUT.SMLConjugateMultiplicity.fieldEquiv => Physics.SMLConjugateMultiplicity.fieldEquiv,
  GUT.SMLConjugateMultiplicity.kernel_dimension => Physics.SMLConjugateMultiplicity.kernel_dimension,
  GUT.SMLConjugateMultiplicity.sourceEquiv => Physics.SMLConjugateMultiplicity.sourceEquiv,
  GUT.SMLConjugateMultiplicity.weakConjugate => Physics.SMLConjugateMultiplicity.weakConjugate
]

assert_compatible GUT.SMLConjugateMultiplicity.actionEquiv => Physics.SMLConjugateMultiplicity.actionEquiv
assert_compatible GUT.SMLConjugateMultiplicity.allowed_iff => Physics.SMLConjugateMultiplicity.allowed_iff
assert_compatible GUT.SMLConjugateMultiplicity.bosonEquiv => Physics.SMLConjugateMultiplicity.bosonEquiv
assert_compatible GUT.SMLConjugateMultiplicity.coefficientEquiv => Physics.SMLConjugateMultiplicity.coefficientEquiv
assert_compatible GUT.SMLConjugateMultiplicity.fieldEquiv => Physics.SMLConjugateMultiplicity.fieldEquiv
assert_compatible GUT.SMLConjugateMultiplicity.kernel_dimension => Physics.SMLConjugateMultiplicity.kernel_dimension
assert_compatible GUT.SMLConjugateMultiplicity.sourceEquiv => Physics.SMLConjugateMultiplicity.sourceEquiv
assert_compatible GUT.SMLConjugateMultiplicity.weakConjugate => Physics.SMLConjugateMultiplicity.weakConjugate
