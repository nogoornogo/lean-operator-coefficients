import GUT.SU6.SelectionRules.Models.ContinuousProfileModel
import GUT.SU6.SelectionRules.Benchmarks.WeylMassFamilyBenchmark
import Physics.StandardModel.Spectrum.Audit.AuditFiniteChargeProfiles

/-! Source-derived profiles, exact legacy recovery, nonlinear mass sources,
and exclusion of the incompatible coefficient-level negative control. -/

set_option autoImplicit false

namespace GUT.AuditContinuousProfileModel

noncomputable section

open ContinuousProfileModel StandardSMCharacterTarget StandardModelLocalOperator

abbrev Residual := Multiplicative (ZMod 2)

def nonlinear : ScalarModel Residual :=
  ScalarModel.ofLegacy (WeylMassFamilyBenchmark.model Residual) (by change (0 : ℤ) < 1; norm_num)

theorem nonlinear_nonzero_mass : nonlinear.sector.mass.form ≠ 0 :=
  WeylMassFamilyBenchmark.mass_nonzero

theorem nonlinear_nonadditive : nonlinear.sector.family.Nonadditive :=
  WeylMassFamilyBenchmark.family_not_additive

theorem nonlinear_radical_dimension : Module.finrank ℂ nonlinear.sector.mass.radical.toSubmodule = 15 :=
  WeylMassFamilyBenchmark.radical_finrank

theorem nonlinear_result :
    nonlinear.geometry.hyperchargePair = (-2, 3) ∧
      FiniteChargeProfiles.OrbitCompatible nonlinear.profile.profiles ∧
      ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator nonlinear.toMassModel.lightSpectrum :=
  ⟨nonlinear.toMassModel.hyperchargePair_eq_standard,
    nonlinear.toMassModel.profiles_compatible, nonlinear.selection_rule_obstruction⟩

/-- The coefficient negative control cannot be an actual model target. -/
theorem incompatible_target_excluded {H : Type*} [CommGroup H]
    (M : Model H) (q : ChargeLabel H) (hq : q ≠ 0)
    (he : M.profile.profiles = (AuditFiniteChargeProfiles.incompatibleFamily q).profiles) : False := by
  have hc := M.profiles_compatible
  rw [he] at hc
  exact AuditFiniteChargeProfiles.incompatible_not_orbitCompatible q hq hc

#print axioms PhysicalProfileSource.forget_profile
#print axioms PhysicalProfileSource.hypercharge_of_dual_profile
#print axioms PhysicalProfileSource.orbitCompatible_of_dual_profile
#print axioms PhysicalProfileSource.dualResolved_of_lightTarget
#print axioms PhysicalProfileSource.source_conclusions
#print axioms Model.hyperchargePair_eq_standard
#print axioms Model.profiles_compatible
#print axioms Model.actual_signature_pair
#print axioms Model.selection_rule_obstruction
#print axioms Model.ofLegacy_mass
#print axioms Model.ofLegacy_lightSpectrum
#print axioms ScalarModel.selection_rule_obstruction
#print axioms ScalarModel.ofLegacy_toMassModel
#print axioms nonlinear_nonzero_mass
#print axioms nonlinear_nonadditive
#print axioms nonlinear_radical_dimension
#print axioms nonlinear_result
#print axioms incompatible_target_excluded

end

end GUT.AuditContinuousProfileModel
