import Physics.FieldTheory.Yukawa.Mass.Audit.AuditWeylMassFamily
import Physics.FieldTheory.Yukawa.WeylMassFamily
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.Audit.AuditWeylMassFamily instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AuditWeylMassFamily.chargedFamily => Physics.AuditWeylMassFamily.chargedFamily,
  GUT.AuditWeylMassFamily.chargedFamily.eq_1 => Physics.AuditWeylMassFamily.chargedFamily.eq_1,
  GUT.AuditWeylMassFamily.chargedFamily_nonzero => Physics.AuditWeylMassFamily.chargedFamily_nonzero,
  GUT.AuditWeylMassFamily.constantSector => Physics.AuditWeylMassFamily.constantSector,
  GUT.AuditWeylMassFamily.constantSector.eq_1 => Physics.AuditWeylMassFamily.constantSector.eq_1,
  GUT.AuditWeylMassFamily.constant_zeroVacuum_nonzero => Physics.AuditWeylMassFamily.constant_zeroVacuum_nonzero,
  GUT.AuditWeylMassFamily.evaluated_mass_not_invariant => Physics.AuditWeylMassFamily.evaluated_mass_not_invariant,
  GUT.AuditWeylMassFamily.minus_one_mem => Physics.AuditWeylMassFamily.minus_one_mem,
  GUT.AuditWeylMassFamily.one_not_fixed => Physics.AuditWeylMassFamily.one_not_fixed,
  GUT.AuditWeylMassFamily.quadraticFamily => Physics.AuditWeylMassFamily.quadraticFamily,
  GUT.AuditWeylMassFamily.quadraticFamily.eq_1 => Physics.AuditWeylMassFamily.quadraticFamily.eq_1,
  GUT.AuditWeylMassFamily.quadraticFamily_not_additive => Physics.AuditWeylMassFamily.quadraticFamily_not_additive,
  GUT.AuditWeylMassFamily.quadraticSector => Physics.AuditWeylMassFamily.quadraticSector,
  GUT.AuditWeylMassFamily.quadraticSector.eq_1 => Physics.AuditWeylMassFamily.quadraticSector.eq_1,
  GUT.AuditWeylMassFamily.quadratic_mass_nonzero => Physics.AuditWeylMassFamily.quadratic_mass_nonzero,
  GUT.AuditWeylMassFamily.subgroupMass => Physics.AuditWeylMassFamily.subgroupMass,
  GUT.AuditWeylMassFamily.subgroupMass.eq_1 => Physics.AuditWeylMassFamily.subgroupMass.eq_1,
  GUT.AuditWeylMassFamily.subgroupMass_invariant => Physics.AuditWeylMassFamily.subgroupMass_invariant,
  GUT.AuditWeylMassFamily.subgroupMass_nonzero => Physics.AuditWeylMassFamily.subgroupMass_nonzero,
  GUT.AuditWeylMassFamily.surviving_action => Physics.AuditWeylMassFamily.surviving_action,
  GUT.AuditWeylMassFamily.two => Physics.AuditWeylMassFamily.two,
  GUT.AuditWeylMassFamily.two.eq_1 => Physics.AuditWeylMassFamily.two.eq_1,
  GUT.AuditWeylMassFamily.two_not_mem => Physics.AuditWeylMassFamily.two_not_mem,
  GUT.AuditWeylMassFamily.unbroken => Physics.AuditWeylMassFamily.unbroken,
  GUT.AuditWeylMassFamily.weight => Physics.AuditWeylMassFamily.weight,
  GUT.AuditWeylMassFamily.weight_apply => Physics.AuditWeylMassFamily.weight_apply,
  GUT.AuditWeylMassFamily.zeroVacuumSector => Physics.AuditWeylMassFamily.zeroVacuumSector,
  GUT.AuditWeylMassFamily.zeroVacuumSector.eq_1 => Physics.AuditWeylMassFamily.zeroVacuumSector.eq_1,
  GUT.AuditWeylMassFamily.zeroVacuum_mass => Physics.AuditWeylMassFamily.zeroVacuum_mass,
  GUT.WeylMassFamily.EquivariantFamily.const.eq_1 => Physics.WeylMassFamily.EquivariantFamily.const.eq_1
]

assert_compatible GUT.AuditWeylMassFamily.chargedFamily => Physics.AuditWeylMassFamily.chargedFamily
assert_compatible GUT.AuditWeylMassFamily.chargedFamily.eq_1 => Physics.AuditWeylMassFamily.chargedFamily.eq_1
assert_compatible GUT.AuditWeylMassFamily.chargedFamily_nonzero => Physics.AuditWeylMassFamily.chargedFamily_nonzero
assert_compatible GUT.AuditWeylMassFamily.constantSector => Physics.AuditWeylMassFamily.constantSector
assert_compatible GUT.AuditWeylMassFamily.constantSector.eq_1 => Physics.AuditWeylMassFamily.constantSector.eq_1
assert_compatible GUT.AuditWeylMassFamily.constant_zeroVacuum_nonzero => Physics.AuditWeylMassFamily.constant_zeroVacuum_nonzero
assert_compatible GUT.AuditWeylMassFamily.evaluated_mass_not_invariant => Physics.AuditWeylMassFamily.evaluated_mass_not_invariant
assert_compatible GUT.AuditWeylMassFamily.minus_one_mem => Physics.AuditWeylMassFamily.minus_one_mem
assert_compatible GUT.AuditWeylMassFamily.one_not_fixed => Physics.AuditWeylMassFamily.one_not_fixed
assert_compatible GUT.AuditWeylMassFamily.quadraticFamily => Physics.AuditWeylMassFamily.quadraticFamily
assert_compatible GUT.AuditWeylMassFamily.quadraticFamily.eq_1 => Physics.AuditWeylMassFamily.quadraticFamily.eq_1
assert_compatible GUT.AuditWeylMassFamily.quadraticFamily_not_additive => Physics.AuditWeylMassFamily.quadraticFamily_not_additive
assert_compatible GUT.AuditWeylMassFamily.quadraticSector => Physics.AuditWeylMassFamily.quadraticSector
assert_compatible GUT.AuditWeylMassFamily.quadraticSector.eq_1 => Physics.AuditWeylMassFamily.quadraticSector.eq_1
assert_compatible GUT.AuditWeylMassFamily.quadratic_mass_nonzero => Physics.AuditWeylMassFamily.quadratic_mass_nonzero
assert_compatible GUT.AuditWeylMassFamily.subgroupMass => Physics.AuditWeylMassFamily.subgroupMass
assert_compatible GUT.AuditWeylMassFamily.subgroupMass.eq_1 => Physics.AuditWeylMassFamily.subgroupMass.eq_1
assert_compatible GUT.AuditWeylMassFamily.subgroupMass_invariant => Physics.AuditWeylMassFamily.subgroupMass_invariant
assert_compatible GUT.AuditWeylMassFamily.subgroupMass_nonzero => Physics.AuditWeylMassFamily.subgroupMass_nonzero
assert_compatible GUT.AuditWeylMassFamily.surviving_action => Physics.AuditWeylMassFamily.surviving_action
assert_compatible GUT.AuditWeylMassFamily.two => Physics.AuditWeylMassFamily.two
assert_compatible GUT.AuditWeylMassFamily.two.eq_1 => Physics.AuditWeylMassFamily.two.eq_1
assert_compatible GUT.AuditWeylMassFamily.two_not_mem => Physics.AuditWeylMassFamily.two_not_mem
assert_compatible GUT.AuditWeylMassFamily.unbroken => Physics.AuditWeylMassFamily.unbroken
assert_compatible GUT.AuditWeylMassFamily.weight => Physics.AuditWeylMassFamily.weight
assert_compatible GUT.AuditWeylMassFamily.weight_apply => Physics.AuditWeylMassFamily.weight_apply
assert_compatible GUT.AuditWeylMassFamily.zeroVacuumSector => Physics.AuditWeylMassFamily.zeroVacuumSector
assert_compatible GUT.AuditWeylMassFamily.zeroVacuumSector.eq_1 => Physics.AuditWeylMassFamily.zeroVacuumSector.eq_1
assert_compatible GUT.AuditWeylMassFamily.zeroVacuum_mass => Physics.AuditWeylMassFamily.zeroVacuum_mass
assert_compatible GUT.WeylMassFamily.EquivariantFamily.const.eq_1 => Physics.WeylMassFamily.EquivariantFamily.const.eq_1
