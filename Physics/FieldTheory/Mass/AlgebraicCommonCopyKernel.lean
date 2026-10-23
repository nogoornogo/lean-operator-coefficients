import Physics.FieldTheory.Mass.Surplus.AlgebraicCommonCopyKernel
import Physics.StandardModel.Operators.QqueSpinorExterior
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.AlgebraicCommonCopyKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AlgebraicCommonCopyKernel.Carrier => Physics.AlgebraicCommonCopyKernel.Carrier,
  GUT.AlgebraicCommonCopyKernel.Components => Physics.AlgebraicCommonCopyKernel.Components,
  GUT.AlgebraicCommonCopyKernel.action => Physics.AlgebraicCommonCopyKernel.action,
  GUT.AlgebraicCommonCopyKernel.exists_common_split => Physics.AlgebraicCommonCopyKernel.exists_common_split,
  GUT.AlgebraicCommonCopyKernel.kernel_physical_exterior => Physics.AlgebraicCommonCopyKernel.kernel_physical_exterior,
  GUT.AlgebraicCommonCopyKernel.kernel_semisimple => Physics.AlgebraicCommonCopyKernel.kernel_semisimple,
  GUT.AlgebraicCommonCopyKernel.ofModuleEquiv => Physics.AlgebraicCommonCopyKernel.ofModuleEquiv,
  GUT.AlgebraicCommonCopyKernel.simpleToKernel => Physics.AlgebraicCommonCopyKernel.simpleToKernel
]

assert_compatible GUT.AlgebraicCommonCopyKernel.Carrier => Physics.AlgebraicCommonCopyKernel.Carrier
assert_compatible GUT.AlgebraicCommonCopyKernel.Components => Physics.AlgebraicCommonCopyKernel.Components
assert_compatible GUT.AlgebraicCommonCopyKernel.action => Physics.AlgebraicCommonCopyKernel.action
assert_compatible GUT.AlgebraicCommonCopyKernel.exists_common_split => Physics.AlgebraicCommonCopyKernel.exists_common_split
assert_compatible GUT.AlgebraicCommonCopyKernel.kernel_physical_exterior => Physics.AlgebraicCommonCopyKernel.kernel_physical_exterior
assert_compatible GUT.AlgebraicCommonCopyKernel.kernel_semisimple => Physics.AlgebraicCommonCopyKernel.kernel_semisimple
assert_compatible GUT.AlgebraicCommonCopyKernel.ofModuleEquiv => Physics.AlgebraicCommonCopyKernel.ofModuleEquiv
assert_compatible GUT.AlgebraicCommonCopyKernel.simpleToKernel => Physics.AlgebraicCommonCopyKernel.simpleToKernel
