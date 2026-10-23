import Physics.FieldTheory.Spinor.Weyl.WeylFiniteKernelControl
import Physics.FieldTheory.Spinor.WeylGeneratorTests
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylFiniteKernelControl instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylFiniteKernelControl.coefficientEquiv => Physics.WeylFiniteKernelControl.coefficientEquiv,
  GUT.WeylFiniteKernelControl.exhaustive => Physics.WeylFiniteKernelControl.exhaustive,
  GUT.WeylFiniteKernelControl.kernel_zero => Physics.WeylFiniteKernelControl.kernel_zero,
  GUT.WeylFiniteKernelControl.lower => Physics.WeylFiniteKernelControl.lower,
  GUT.WeylFiniteKernelControl.tests => Physics.WeylFiniteKernelControl.tests,
  GUT.WeylFiniteKernelControl.tests.eq_1 => Physics.WeylFiniteKernelControl.tests.eq_1,
  GUT.WeylFiniteKernelControl.tests_force_zero => Physics.WeylFiniteKernelControl.tests_force_zero,
  GUT.WeylFiniteKernelControl.upper => Physics.WeylFiniteKernelControl.upper
]

assert_compatible GUT.WeylFiniteKernelControl.coefficientEquiv => Physics.WeylFiniteKernelControl.coefficientEquiv
assert_compatible GUT.WeylFiniteKernelControl.exhaustive => Physics.WeylFiniteKernelControl.exhaustive
assert_compatible GUT.WeylFiniteKernelControl.kernel_zero => Physics.WeylFiniteKernelControl.kernel_zero
assert_compatible GUT.WeylFiniteKernelControl.lower => Physics.WeylFiniteKernelControl.lower
assert_compatible GUT.WeylFiniteKernelControl.tests => Physics.WeylFiniteKernelControl.tests
assert_compatible GUT.WeylFiniteKernelControl.tests.eq_1 => Physics.WeylFiniteKernelControl.tests.eq_1
assert_compatible GUT.WeylFiniteKernelControl.tests_force_zero => Physics.WeylFiniteKernelControl.tests_force_zero
assert_compatible GUT.WeylFiniteKernelControl.upper => Physics.WeylFiniteKernelControl.upper
