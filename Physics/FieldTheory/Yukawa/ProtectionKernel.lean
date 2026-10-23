import Physics.FieldTheory.Yukawa.Mass.ProtectionKernel
import Physics.FieldTheory.Yukawa.VacuumMassProtection
import Physics.FieldTheory.Yukawa.YukawaClassification
import Physics.FieldTheory.Mass.ExactRadical
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.ProtectionKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.YukawaProtectionKernel.exists_iff_range => Physics.YukawaProtectionKernel.exists_iff_range,
  GUT.YukawaProtectionKernel.family => Physics.YukawaProtectionKernel.family,
  GUT.YukawaProtectionKernel.family_protected_iff => Physics.YukawaProtectionKernel.family_protected_iff,
  GUT.YukawaProtectionKernel.fiber_iff => Physics.YukawaProtectionKernel.fiber_iff,
  GUT.YukawaProtectionKernel.generated_exact_iff => Physics.YukawaProtectionKernel.generated_exact_iff,
  GUT.YukawaProtectionKernel.obstruction => Physics.YukawaProtectionKernel.obstruction,
  GUT.YukawaProtectionKernel.offset => Physics.YukawaProtectionKernel.offset,
  GUT.YukawaProtectionKernel.protected_fiber_iff => Physics.YukawaProtectionKernel.protected_fiber_iff,
  GUT.YukawaProtectionKernel.protected_iff => Physics.YukawaProtectionKernel.protected_iff,
  GUT.YukawaProtectionKernel.protected_iff_mem_kernel => Physics.YukawaProtectionKernel.protected_iff_mem_kernel,
  GUT.YukawaProtectionKernel.universal_iff => Physics.YukawaProtectionKernel.universal_iff
]

assert_compatible GUT.YukawaProtectionKernel.exists_iff_range => Physics.YukawaProtectionKernel.exists_iff_range
assert_compatible GUT.YukawaProtectionKernel.family => Physics.YukawaProtectionKernel.family
assert_compatible GUT.YukawaProtectionKernel.family_protected_iff => Physics.YukawaProtectionKernel.family_protected_iff
assert_compatible GUT.YukawaProtectionKernel.fiber_iff => Physics.YukawaProtectionKernel.fiber_iff
assert_compatible GUT.YukawaProtectionKernel.generated_exact_iff => Physics.YukawaProtectionKernel.generated_exact_iff
assert_compatible GUT.YukawaProtectionKernel.obstruction => Physics.YukawaProtectionKernel.obstruction
assert_compatible GUT.YukawaProtectionKernel.offset => Physics.YukawaProtectionKernel.offset
assert_compatible GUT.YukawaProtectionKernel.protected_fiber_iff => Physics.YukawaProtectionKernel.protected_fiber_iff
assert_compatible GUT.YukawaProtectionKernel.protected_iff => Physics.YukawaProtectionKernel.protected_iff
assert_compatible GUT.YukawaProtectionKernel.protected_iff_mem_kernel => Physics.YukawaProtectionKernel.protected_iff_mem_kernel
assert_compatible GUT.YukawaProtectionKernel.universal_iff => Physics.YukawaProtectionKernel.universal_iff
