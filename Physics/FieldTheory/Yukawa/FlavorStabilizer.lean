import Physics.FieldTheory.Yukawa.Actions.FlavorStabilizer
import Math.RepresentationTheory.FamilyStabilizer
import Physics.FieldTheory.Yukawa.SymmetricScalarYukawa
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Actions.FlavorStabilizer instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavorStabilizer.couplingAction => Physics.FlavorStabilizer.couplingAction,
  GUT.FlavorStabilizer.couplingAction.eq_1 => Physics.FlavorStabilizer.couplingAction.eq_1,
  GUT.FlavorStabilizer.couplingSubgroup => Physics.FlavorStabilizer.couplingSubgroup,
  GUT.FlavorStabilizer.coupling_mem_iff => Physics.FlavorStabilizer.coupling_mem_iff,
  GUT.FlavorStabilizer.coupling_of_generating_masses => Physics.FlavorStabilizer.coupling_of_generating_masses,
  GUT.FlavorStabilizer.dataSubgroup => Physics.FlavorStabilizer.dataSubgroup,
  GUT.FlavorStabilizer.data_mem_iff => Physics.FlavorStabilizer.data_mem_iff,
  GUT.FlavorStabilizer.defect => Physics.FlavorStabilizer.defect,
  GUT.FlavorStabilizer.defect.eq_1 => Physics.FlavorStabilizer.defect.eq_1,
  GUT.FlavorStabilizer.defect_zero_iff => Physics.FlavorStabilizer.defect_zero_iff,
  GUT.FlavorStabilizer.defect_zero_of_generators => Physics.FlavorStabilizer.defect_zero_of_generators,
  GUT.FlavorStabilizer.equality_iff_no_hidden_defect => Physics.FlavorStabilizer.equality_iff_no_hidden_defect,
  GUT.FlavorStabilizer.formAction => Physics.FlavorStabilizer.formAction,
  GUT.FlavorStabilizer.fullSubgroup => Physics.FlavorStabilizer.fullSubgroup,
  GUT.FlavorStabilizer.full_le_mass => Physics.FlavorStabilizer.full_le_mass,
  GUT.FlavorStabilizer.massSubgroup => Physics.FlavorStabilizer.massSubgroup,
  GUT.FlavorStabilizer.mass_iff_defect_at_vacuum => Physics.FlavorStabilizer.mass_iff_defect_at_vacuum,
  GUT.FlavorStabilizer.mass_mem_iff => Physics.FlavorStabilizer.mass_mem_iff,
  GUT.FlavorStabilizer.residualHomEquiv => Physics.FlavorStabilizer.residualHomEquiv,
  GUT.FlavorStabilizer.restrictedVacuum => Physics.FlavorStabilizer.restrictedVacuum,
  GUT.FlavorStabilizer.restrictedVacuum.eq_1 => Physics.FlavorStabilizer.restrictedVacuum.eq_1,
  GUT.FlavorStabilizer.restrictedYukawa => Physics.FlavorStabilizer.restrictedYukawa,
  GUT.FlavorStabilizer.restrictedYukawa.eq_1 => Physics.FlavorStabilizer.restrictedYukawa.eq_1,
  GUT.FlavorStabilizer.sector => Physics.FlavorStabilizer.sector,
  GUT.FlavorStabilizer.sector.eq_1 => Physics.FlavorStabilizer.sector.eq_1,
  GUT.FlavorStabilizer.sector_mass => Physics.FlavorStabilizer.sector_mass,
  GUT.FlavorStabilizer.vacuumSubgroup => Physics.FlavorStabilizer.vacuumSubgroup
]

assert_compatible GUT.FlavorStabilizer.couplingAction => Physics.FlavorStabilizer.couplingAction
assert_compatible GUT.FlavorStabilizer.couplingAction.eq_1 => Physics.FlavorStabilizer.couplingAction.eq_1
assert_compatible GUT.FlavorStabilizer.couplingSubgroup => Physics.FlavorStabilizer.couplingSubgroup
assert_compatible GUT.FlavorStabilizer.coupling_mem_iff => Physics.FlavorStabilizer.coupling_mem_iff
assert_compatible GUT.FlavorStabilizer.coupling_of_generating_masses => Physics.FlavorStabilizer.coupling_of_generating_masses
assert_compatible GUT.FlavorStabilizer.dataSubgroup => Physics.FlavorStabilizer.dataSubgroup
assert_compatible GUT.FlavorStabilizer.data_mem_iff => Physics.FlavorStabilizer.data_mem_iff
assert_compatible GUT.FlavorStabilizer.defect => Physics.FlavorStabilizer.defect
assert_compatible GUT.FlavorStabilizer.defect.eq_1 => Physics.FlavorStabilizer.defect.eq_1
assert_compatible GUT.FlavorStabilizer.defect_zero_iff => Physics.FlavorStabilizer.defect_zero_iff
assert_compatible GUT.FlavorStabilizer.defect_zero_of_generators => Physics.FlavorStabilizer.defect_zero_of_generators
assert_compatible GUT.FlavorStabilizer.equality_iff_no_hidden_defect => Physics.FlavorStabilizer.equality_iff_no_hidden_defect
assert_compatible GUT.FlavorStabilizer.formAction => Physics.FlavorStabilizer.formAction
assert_compatible GUT.FlavorStabilizer.fullSubgroup => Physics.FlavorStabilizer.fullSubgroup
assert_compatible GUT.FlavorStabilizer.full_le_mass => Physics.FlavorStabilizer.full_le_mass
assert_compatible GUT.FlavorStabilizer.massSubgroup => Physics.FlavorStabilizer.massSubgroup
assert_compatible GUT.FlavorStabilizer.mass_iff_defect_at_vacuum => Physics.FlavorStabilizer.mass_iff_defect_at_vacuum
assert_compatible GUT.FlavorStabilizer.mass_mem_iff => Physics.FlavorStabilizer.mass_mem_iff
assert_compatible GUT.FlavorStabilizer.residualHomEquiv => Physics.FlavorStabilizer.residualHomEquiv
assert_compatible GUT.FlavorStabilizer.restrictedVacuum => Physics.FlavorStabilizer.restrictedVacuum
assert_compatible GUT.FlavorStabilizer.restrictedVacuum.eq_1 => Physics.FlavorStabilizer.restrictedVacuum.eq_1
assert_compatible GUT.FlavorStabilizer.restrictedYukawa => Physics.FlavorStabilizer.restrictedYukawa
assert_compatible GUT.FlavorStabilizer.restrictedYukawa.eq_1 => Physics.FlavorStabilizer.restrictedYukawa.eq_1
assert_compatible GUT.FlavorStabilizer.sector => Physics.FlavorStabilizer.sector
assert_compatible GUT.FlavorStabilizer.sector.eq_1 => Physics.FlavorStabilizer.sector.eq_1
assert_compatible GUT.FlavorStabilizer.sector_mass => Physics.FlavorStabilizer.sector_mass
assert_compatible GUT.FlavorStabilizer.vacuumSubgroup => Physics.FlavorStabilizer.vacuumSubgroup
