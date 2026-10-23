import Physics.FieldTheory.Yukawa.Mass.MultilinearWeylMassContinuity
import Physics.FieldTheory.Yukawa.MultilinearWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.MultilinearWeylMassContinuity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylMassFamily.EquivariantFamily.continuous_sum => Physics.WeylMassFamily.EquivariantFamily.continuous_sum,
  GUT.WeylMassFamily.MultilinearCoupling.continuous_coefficient => Physics.WeylMassFamily.MultilinearCoupling.continuous_coefficient,
  GUT.WeylMassFamily.MultilinearCoupling.continuous_toFamily => Physics.WeylMassFamily.MultilinearCoupling.continuous_toFamily,
  GUT.WeylMassFamily.continuous_multilinear_scalar => Physics.WeylMassFamily.continuous_multilinear_scalar,
  GUT.WeylMassFamily.multilinear_basis_expansion => Physics.WeylMassFamily.multilinear_basis_expansion
]

assert_compatible GUT.WeylMassFamily.EquivariantFamily.continuous_sum => Physics.WeylMassFamily.EquivariantFamily.continuous_sum
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.continuous_coefficient => Physics.WeylMassFamily.MultilinearCoupling.continuous_coefficient
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.continuous_toFamily => Physics.WeylMassFamily.MultilinearCoupling.continuous_toFamily
assert_compatible GUT.WeylMassFamily.continuous_multilinear_scalar => Physics.WeylMassFamily.continuous_multilinear_scalar
assert_compatible GUT.WeylMassFamily.multilinear_basis_expansion => Physics.WeylMassFamily.multilinear_basis_expansion
