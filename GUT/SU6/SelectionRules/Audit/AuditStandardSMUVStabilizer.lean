import GUT.SU6.SelectionRules.Models.StandardSMUVStabilizer

open Physics

/-! Persistent audit: the existing nonzero 15-mode benchmark VEV has a
stabilizer strictly larger than the standard SM image. The mass and VEV
are not replaced, and neither a scalar potential nor an amplitude is assumed. -/

set_option autoImplicit false

namespace GUT.AuditStandardSMUVStabilizer

noncomputable section

open StandardSMUVStabilizer

theorem explicit_witness (H : Type*) [CommGroup H] :
    rotation ∉ StandardSMGroup.hom.range ∧
      StandardSMUVYukawa.scalar.rho rotation (StandardSMUVYukawa.vacuum H) =
        StandardSMUVYukawa.vacuum H :=
  ⟨rotation_not_standard, vacuum_rotation H⟩

theorem benchmark_retained (H : Type*) [CommGroup H] :
    StandardSMUVYukawa.vacuum H ≠ 0 ∧
      (StandardSMUVYukawa.mass H).form ≠ 0 ∧
      Module.finrank ℂ (StandardSMUVYukawa.mass H).radical.toSubmodule = 15 ∧
      StandardSMGroup.hom.range <
        WeylYukawaMass.vacuumStabilizer StandardSMUVYukawa.scalar.rho
          (StandardSMUVYukawa.vacuum H) :=
  ⟨StandardSMUVYukawa.vacuum_nonzero H, StandardSMUVYukawa.mass_nonzero H,
    StandardSMUVYukawa.radical_finrank H, standard_lt_stabilizer H⟩

example : ∃ g : ActualRestriction.SU6, g ∉ StandardSMGroup.hom.range ∧
    StandardSMUVYukawa.scalar.rho g (StandardSMUVYukawa.vacuum Unit) =
      StandardSMUVYukawa.vacuum Unit := exists_extra_stabilizer Unit

example : ∃ g : ActualRestriction.SU6, g ∉ StandardSMGroup.hom.range ∧
    StandardSMUVYukawa.scalar.rho g (StandardSMUVYukawa.vacuum (Multiplicative (ZMod 2))) =
      StandardSMUVYukawa.vacuum (Multiplicative (ZMod 2)) := exists_extra_stabilizer _

theorem not_exact_SM (H : Type*) [CommGroup H] :
    StandardSMGroup.hom.range ≠
      WeylYukawaMass.vacuumStabilizer StandardSMUVYukawa.scalar.rho
        (StandardSMUVYukawa.vacuum H) := ne_of_lt (standard_lt_stabilizer H)

#print axioms StandardSMUVCoordinates.withResidualEquiv_linear
#print axioms StandardSMUVCoordinates.antifundamentalEquiv_linear
#print axioms StandardSMUVCoordinates.mass_form_gauge
#print axioms rotation_apply
#print axioms contract_covariant
#print axioms mass_formula
#print axioms mass_rotation
#print axioms vacuum_fixed_iff
#print axioms rotation_not_standard
#print axioms explicit_witness
#print axioms exists_extra_stabilizer
#print axioms standard_lt_stabilizer
#print axioms benchmark_retained
#print axioms not_exact_SM

end

end GUT.AuditStandardSMUVStabilizer
