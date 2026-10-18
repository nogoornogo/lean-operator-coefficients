import GUT.SU6.SelectionRules.Models.CanonicalChainModel
import GUT.SU6.SelectionRules.Audit.AuditContinuousProfileModel
import GUT.SU6.SelectionRules.Benchmarks.NonuniformProfileModel

/-! Actual legacy source regressions: the nonlinear nonzero mass with
fifteen zero modes, and a two-charge example retaining extra zero modes. -/

set_option autoImplicit false

namespace GUT.SU6.AuditCanonicalChainModel

noncomputable section

open CanonicalChainModel StandardModelLocalOperator

/-- The physical torus covering used for descent is genuinely not an
invertible coordinate chart, despite the injective SU(5) block inclusion. -/
theorem torusCover_not_injective : ¬ Function.Injective SU5TorusCompatibility.torusCover := by
  let z : SU5.PhysicalTorus.Coordinates := ![1, 1, -1, -1]
  have h0 : z 0 = 1 := rfl
  have h1 : z 1 = 1 := rfl
  have h2 : z 2 = -1 := rfl
  have h3 : z 3 = -1 := rfl
  have hz : SU5.PhysicalTorus.toTorus z = 1 := by
    apply Subtype.ext
    ext i
    fin_cases i <;> norm_num [SU5.PhysicalTorus.toTorus, SU5.PhysicalTorus.entries, h0, h1, h2, h3]
  have hn : z ≠ 1 := by
    intro he
    have hv := congrArg (fun w : SU5.PhysicalTorus.Coordinates => (w 3 : ℂ)) he
    change ((-1 : Circle) : ℂ) = 1 at hv
    norm_num at hv
  obtain ⟨x, hx⟩ := SU5TorusCompatibility.circleCoordinates_surjective z
  intro hi
  have he : SU5TorusCompatibility.torusCover x = SU5TorusCompatibility.torusCover 1 := by
    rw [map_one]
    change SU5.PhysicalTorus.toTorus (SU5TorusCompatibility.circleCoordinates x) = 1
    rw [hx, hz]
  apply hn
  rw [← hx, hi he, map_one]

def nonlinear := model AuditContinuousProfileModel.nonlinear.toMassModel

theorem nonlinear_spectrum :
    nonlinear.lightSpectrum = AuditContinuousProfileModel.nonlinear.toMassModel.lightSpectrum :=
  spectrum_compatible _

theorem nonlinear_mass_nonzero : nonlinear.mass.form ≠ 0 :=
  (mass_nonzero_iff _).mpr AuditContinuousProfileModel.nonlinear_nonzero_mass

theorem nonlinear_radical_finrank : Module.finrank ℂ nonlinear.mass.radical.toSubmodule = 15 :=
  (radical_finrank _).trans AuditContinuousProfileModel.nonlinear_radical_dimension

def nonuniform := model NonuniformProfileModel.nonuniform

theorem nonuniform_spectrum : nonuniform.lightSpectrum = NonuniformProfileModel.nonuniform.lightSpectrum :=
  spectrum_compatible _

theorem nonuniform_radical_finrank : Module.finrank ℂ nonuniform.mass.radical.toSubmodule = 54 :=
  (radical_finrank _).trans NonuniformProfileModel.nonuniform_result.2.1

theorem nonuniform_not_pure :
    ¬ ∃ k, nonuniform.profile.profiles = FiniteChargeProfiles.pure 2 k := by
  change ¬ ∃ k, (model NonuniformProfileModel.nonuniform).profile.profiles = _
  rw [model_profile]
  exact NonuniformProfileModel.nonuniform_not_pure

theorem both_obstructions :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator nonlinear.lightSpectrum ∧
      ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator nonuniform.lightSpectrum :=
  ⟨nonlinear.selection_rule_obstruction, nonuniform.selection_rule_obstruction⟩

#print axioms UnitaryVirtualRealization.ActualUnitaryGroupRepresentation.restrict_copies
#print axioms UnitaryVirtualRealization.FiniteUnitaryVirtualRepresentation.restrict_positive
#print axioms ChargedAmbientRealization.restrict_summand
#print axioms ChargedAmbientRealization.restrict_positive
#print axioms StandardSU5Inclusion.inclusion_injective
#print axioms StandardSU5Inclusion.inclusion_continuous
#print axioms StandardSU5Inclusion.inclusion_torus
#print axioms SU5TorusCompatibility.cover_surjective
#print axioms SU5TorusCompatibility.key_comp_cover
#print axioms torusCover_not_injective
#print axioms PhysicalChainSource.action_comp
#print axioms PhysicalChainSource.mass_form
#print axioms PhysicalChainSource.radical_comp
#print axioms PhysicalChainSource.hasTarget
#print axioms PhysicalChainSource.spectrum_eq
#print axioms fields_eq
#print axioms CanonicalChainTransport.ofEq
#print axioms conversion
#print axioms fieldEquiv
#print axioms model
#print axioms model_profile
#print axioms model_singlets
#print axioms continuousModel
#print axioms action_compatible
#print axioms mass_compatible
#print axioms mass_nonzero_iff
#print axioms radicalEquiv
#print axioms radicalEquiv_apply
#print axioms radical_character
#print axioms radical_finrank
#print axioms spectrum_compatible
#print axioms CanonicalChainModel.selection_rule_obstruction
#print axioms scalar_mass_compatible
#print axioms nonlinear_mass_nonzero
#print axioms nonlinear_radical_finrank
#print axioms nonlinear_spectrum
#print axioms nonuniform_spectrum
#print axioms nonuniform_radical_finrank
#print axioms nonuniform_not_pure
#print axioms both_obstructions

end

end GUT.SU6.AuditCanonicalChainModel
