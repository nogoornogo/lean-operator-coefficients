import Physics.FieldTheory.Yukawa.Mass.WeylMassFamilyCompatibility
import Physics.FieldTheory.Yukawa.MultilinearWeylMass
import Physics.FieldTheory.Yukawa.WeylYukawaMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.WeylMassFamilyCompatibility instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylYukawaMass.EquivariantYukawa.toFamily => Physics.WeylYukawaMass.EquivariantYukawa.toFamily,
  GUT.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling => Physics.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling,
  GUT.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling_toFamily => Physics.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling_toFamily,
  GUT.WeylYukawaMass.Sector.ofBareMass_toFamilySector => Physics.WeylYukawaMass.Sector.ofBareMass_toFamilySector,
  GUT.WeylYukawaMass.Sector.toFamilySector => Physics.WeylYukawaMass.Sector.toFamilySector,
  GUT.WeylYukawaMass.Sector.toFamilySector_mass => Physics.WeylYukawaMass.Sector.toFamilySector_mass,
  GUT.WeylYukawaMass.toFamily_atVacuumOn => Physics.WeylYukawaMass.toFamily_atVacuumOn,
  GUT.WeylYukawaMass.toFamily_atVacuumStabilizer => Physics.WeylYukawaMass.toFamily_atVacuumStabilizer,
  GUT.WeylYukawaMass.toMultilinearCoupling_atVacuumOn => Physics.WeylYukawaMass.toMultilinearCoupling_atVacuumOn
]

assert_compatible GUT.WeylYukawaMass.EquivariantYukawa.toFamily => Physics.WeylYukawaMass.EquivariantYukawa.toFamily
assert_compatible GUT.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling => Physics.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling
assert_compatible GUT.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling_toFamily => Physics.WeylYukawaMass.EquivariantYukawa.toMultilinearCoupling_toFamily
assert_compatible GUT.WeylYukawaMass.Sector.ofBareMass_toFamilySector => Physics.WeylYukawaMass.Sector.ofBareMass_toFamilySector
assert_compatible GUT.WeylYukawaMass.Sector.toFamilySector => Physics.WeylYukawaMass.Sector.toFamilySector
assert_compatible GUT.WeylYukawaMass.Sector.toFamilySector_mass => Physics.WeylYukawaMass.Sector.toFamilySector_mass
assert_compatible GUT.WeylYukawaMass.toFamily_atVacuumOn => Physics.WeylYukawaMass.toFamily_atVacuumOn
assert_compatible GUT.WeylYukawaMass.toFamily_atVacuumStabilizer => Physics.WeylYukawaMass.toFamily_atVacuumStabilizer
assert_compatible GUT.WeylYukawaMass.toMultilinearCoupling_atVacuumOn => Physics.WeylYukawaMass.toMultilinearCoupling_atVacuumOn
