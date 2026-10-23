import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel
import Physics.StandardModel.Operators.SMIntegralLocalWeights
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFullLocalKernel.Carrier => Physics.SMFullLocalKernel.Carrier,
  GUT.SMFullLocalKernel.Index => Physics.SMFullLocalKernel.Index,
  GUT.SMFullLocalKernel.Kernel => Physics.SMFullLocalKernel.Kernel,
  GUT.SMFullLocalKernel.allowed_iff_rank_lt => Physics.SMFullLocalKernel.allowed_iff_rank_lt,
  GUT.SMFullLocalKernel.basis => Physics.SMFullLocalKernel.basis,
  GUT.SMFullLocalKernel.card_tests => Physics.SMFullLocalKernel.card_tests,
  GUT.SMFullLocalKernel.coefficientEquiv => Physics.SMFullLocalKernel.coefficientEquiv,
  GUT.SMFullLocalKernel.constraints => Physics.SMFullLocalKernel.constraints,
  GUT.SMFullLocalKernel.exhaustive => Physics.SMFullLocalKernel.exhaustive,
  GUT.SMFullLocalKernel.matrix => Physics.SMFullLocalKernel.matrix,
  GUT.SMFullLocalKernel.tests => Physics.SMFullLocalKernel.tests,
  GUT.SMIntegralLocalWeights.hyper.eq_1 => Physics.SMIntegralLocalWeights.hyper.eq_1,
  GUT.SMIntegralLocalWeights.spin.eq_1 => Physics.SMIntegralLocalWeights.spin.eq_1
]

assert_compatible GUT.SMFullLocalKernel.Carrier => Physics.SMFullLocalKernel.Carrier
assert_compatible GUT.SMFullLocalKernel.Index => Physics.SMFullLocalKernel.Index
assert_compatible GUT.SMFullLocalKernel.Kernel => Physics.SMFullLocalKernel.Kernel
assert_compatible GUT.SMFullLocalKernel.allowed_iff_rank_lt => Physics.SMFullLocalKernel.allowed_iff_rank_lt
assert_compatible GUT.SMFullLocalKernel.basis => Physics.SMFullLocalKernel.basis
assert_compatible GUT.SMFullLocalKernel.card_tests => Physics.SMFullLocalKernel.card_tests
assert_compatible GUT.SMFullLocalKernel.coefficientEquiv => Physics.SMFullLocalKernel.coefficientEquiv
assert_compatible GUT.SMFullLocalKernel.constraints => Physics.SMFullLocalKernel.constraints
assert_compatible GUT.SMFullLocalKernel.exhaustive => Physics.SMFullLocalKernel.exhaustive
assert_compatible GUT.SMFullLocalKernel.matrix => Physics.SMFullLocalKernel.matrix
assert_compatible GUT.SMFullLocalKernel.tests => Physics.SMFullLocalKernel.tests
assert_compatible GUT.SMIntegralLocalWeights.hyper.eq_1 => Physics.SMIntegralLocalWeights.hyper.eq_1
assert_compatible GUT.SMIntegralLocalWeights.spin.eq_1 => Physics.SMIntegralLocalWeights.spin.eq_1
