import Physics.StandardModel.Operators.Support.Coordinates.SMRationalLocalKernel
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.RepresentationTheory.RationalCompactTests
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMRationalLocalKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMRationalLocalKernel.Carrier => Physics.SMRationalLocalKernel.Carrier,
  GUT.SMRationalLocalKernel.Index => Physics.SMRationalLocalKernel.Index,
  GUT.SMRationalLocalKernel.Kernel => Physics.SMRationalLocalKernel.Kernel,
  GUT.SMRationalLocalKernel.allowed_iff_rank_lt => Physics.SMRationalLocalKernel.allowed_iff_rank_lt,
  GUT.SMRationalLocalKernel.basis => Physics.SMRationalLocalKernel.basis,
  GUT.SMRationalLocalKernel.card_tests => Physics.SMRationalLocalKernel.card_tests,
  GUT.SMRationalLocalKernel.coefficientEquiv => Physics.SMRationalLocalKernel.coefficientEquiv,
  GUT.SMRationalLocalKernel.constraints => Physics.SMRationalLocalKernel.constraints,
  GUT.SMRationalLocalKernel.exhaustive => Physics.SMRationalLocalKernel.exhaustive,
  GUT.SMRationalLocalKernel.matrix => Physics.SMRationalLocalKernel.matrix,
  GUT.SMRationalLocalKernel.tests => Physics.SMRationalLocalKernel.tests
]

assert_compatible GUT.SMRationalLocalKernel.Carrier => Physics.SMRationalLocalKernel.Carrier
assert_compatible GUT.SMRationalLocalKernel.Index => Physics.SMRationalLocalKernel.Index
assert_compatible GUT.SMRationalLocalKernel.Kernel => Physics.SMRationalLocalKernel.Kernel
assert_compatible GUT.SMRationalLocalKernel.allowed_iff_rank_lt => Physics.SMRationalLocalKernel.allowed_iff_rank_lt
assert_compatible GUT.SMRationalLocalKernel.basis => Physics.SMRationalLocalKernel.basis
assert_compatible GUT.SMRationalLocalKernel.card_tests => Physics.SMRationalLocalKernel.card_tests
assert_compatible GUT.SMRationalLocalKernel.coefficientEquiv => Physics.SMRationalLocalKernel.coefficientEquiv
assert_compatible GUT.SMRationalLocalKernel.constraints => Physics.SMRationalLocalKernel.constraints
assert_compatible GUT.SMRationalLocalKernel.exhaustive => Physics.SMRationalLocalKernel.exhaustive
assert_compatible GUT.SMRationalLocalKernel.matrix => Physics.SMRationalLocalKernel.matrix
assert_compatible GUT.SMRationalLocalKernel.tests => Physics.SMRationalLocalKernel.tests
