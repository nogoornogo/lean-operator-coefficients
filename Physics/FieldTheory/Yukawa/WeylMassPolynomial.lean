import Physics.FieldTheory.Yukawa.Mass.WeylMassPolynomial
import Physics.FieldTheory.Yukawa.MultilinearWeylMassContinuity
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.WeylMassPolynomial instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylMassFamily.EquivariantFamily.Nonadditive => Physics.WeylMassFamily.EquivariantFamily.Nonadditive,
  GUT.WeylMassFamily.EquivariantFamily.continuous_powerOfMass => Physics.WeylMassFamily.EquivariantFamily.continuous_powerOfMass,
  GUT.WeylMassFamily.EquivariantFamily.powerOfMass => Physics.WeylMassFamily.EquivariantFamily.powerOfMass,
  GUT.WeylMassFamily.EquivariantFamily.powerOfMass_apply => Physics.WeylMassFamily.EquivariantFamily.powerOfMass_apply,
  GUT.WeylMassFamily.EquivariantFamily.powerOfMass_nonzero => Physics.WeylMassFamily.EquivariantFamily.powerOfMass_nonzero,
  GUT.WeylMassFamily.EquivariantFamily.powerOfMass_zero => Physics.WeylMassFamily.EquivariantFamily.powerOfMass_zero,
  GUT.WeylMassFamily.EquivariantFamily.quadratic_nonadditive => Physics.WeylMassFamily.EquivariantFamily.quadratic_nonadditive,
  GUT.WeylMassFamily.EquivariantFamily.quadratic_not_additive => Physics.WeylMassFamily.EquivariantFamily.quadratic_not_additive,
  GUT.WeylMassFamily.MultilinearCoupling.powerOfMass => Physics.WeylMassFamily.MultilinearCoupling.powerOfMass,
  GUT.WeylMassFamily.Sector.ofMassAsPower => Physics.WeylMassFamily.Sector.ofMassAsPower,
  GUT.WeylMassFamily.Sector.ofMassAsPower.eq_1 => Physics.WeylMassFamily.Sector.ofMassAsPower.eq_1,
  GUT.WeylMassFamily.Sector.ofMassAsPower_mass => Physics.WeylMassFamily.Sector.ofMassAsPower_mass,
  GUT.WeylMassFamily.Sector.ofMassAsPower_zeroVacuum => Physics.WeylMassFamily.Sector.ofMassAsPower_zeroVacuum
]

assert_compatible GUT.WeylMassFamily.EquivariantFamily.Nonadditive => Physics.WeylMassFamily.EquivariantFamily.Nonadditive
assert_compatible GUT.WeylMassFamily.EquivariantFamily.continuous_powerOfMass => Physics.WeylMassFamily.EquivariantFamily.continuous_powerOfMass
assert_compatible GUT.WeylMassFamily.EquivariantFamily.powerOfMass => Physics.WeylMassFamily.EquivariantFamily.powerOfMass
assert_compatible GUT.WeylMassFamily.EquivariantFamily.powerOfMass_apply => Physics.WeylMassFamily.EquivariantFamily.powerOfMass_apply
assert_compatible GUT.WeylMassFamily.EquivariantFamily.powerOfMass_nonzero => Physics.WeylMassFamily.EquivariantFamily.powerOfMass_nonzero
assert_compatible GUT.WeylMassFamily.EquivariantFamily.powerOfMass_zero => Physics.WeylMassFamily.EquivariantFamily.powerOfMass_zero
assert_compatible GUT.WeylMassFamily.EquivariantFamily.quadratic_nonadditive => Physics.WeylMassFamily.EquivariantFamily.quadratic_nonadditive
assert_compatible GUT.WeylMassFamily.EquivariantFamily.quadratic_not_additive => Physics.WeylMassFamily.EquivariantFamily.quadratic_not_additive
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.powerOfMass => Physics.WeylMassFamily.MultilinearCoupling.powerOfMass
assert_compatible GUT.WeylMassFamily.Sector.ofMassAsPower => Physics.WeylMassFamily.Sector.ofMassAsPower
assert_compatible GUT.WeylMassFamily.Sector.ofMassAsPower.eq_1 => Physics.WeylMassFamily.Sector.ofMassAsPower.eq_1
assert_compatible GUT.WeylMassFamily.Sector.ofMassAsPower_mass => Physics.WeylMassFamily.Sector.ofMassAsPower_mass
assert_compatible GUT.WeylMassFamily.Sector.ofMassAsPower_zeroVacuum => Physics.WeylMassFamily.Sector.ofMassAsPower_zeroVacuum
