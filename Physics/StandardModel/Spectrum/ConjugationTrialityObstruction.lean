import Physics.StandardModel.Spectrum.ConjugationMassSource
import Physics.StandardModel.Spectrum.LeptonTrialitySpectrum

open Math

/-! Negative control for the structural criterion. The actual triality source
cannot extend, with its restricted action unchanged, to a source admitting all
three conjugations. This is not an obstruction to embedding the torus alone. -/

set_option autoImplicit false

namespace GUT.StructuralConjugationTriality

noncomputable section
open SU5 SU5.MaximalTorus StructuralConjugation
open StandardAbelianCharge StandardWeylDualTarget FiniteAbelianChargeSectors
open FiniteChargeProfiles InvariantWeylMass LeptonTriality

theorem family_not_compatible : ¬ OrbitCompatible family.profiles := by
  intro hc
  have he := congrArg (fun p : ChargeLabel Residual →₀ ℕ => p label) hc.2.2
  norm_num [family, FiniteChargeProfiles.pure, assignment, charges,
    label_ne_zero, Ne.symm label_ne_zero] at he

theorem target_with_zero : targetWithSinglets family.profiles (0 : ChargeLabel Residual →₀ ℤ) =
    LeptonTriality.spectrum := by
  simp [targetWithSinglets, StandardSMCharacterTarget.singletResolvedCharacter,
    LeptonTriality.spectrum]

section Source
variable {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
  [FiniteDimensional ℂ E] (j : Torus →* G) (rho : Representation ℂ (G × Residual) E)

theorem no_conjugations_of_dual_target
    (ht : ∀ g, (restrict j rho).character g - (restrict j rho).dual.character g =
      TorusCharacter.eval (chiralDifference LeptonTriality.spectrum) g) :
    ¬ Nonempty (ThreeConjugations j) := by
  rintro ⟨c⟩
  apply family_not_compatible
  apply StructuralConjugation.profiles_compatible c rho family.profiles 0
  simpa only [target_with_zero] using ht

end Source

section Mass
variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] (j : Torus →* G) (rho : Representation ℂ (G × Residual) E)
  (B : SymmetricMass (restrict j rho))

/-- Even the dual light target already excludes all three conjugations;
no equality of full spectra or absence of vectorlike modes is needed. -/
theorem no_conjugations_of_light_target
    (ht : StructuralConjugationMass.HasTarget j rho B family.profiles 0) :
    ¬ Nonempty (ThreeConjugations j) := by
  rintro ⟨c⟩
  exact family_not_compatible
    (StructuralConjugationMass.profiles_compatible j rho B family.profiles 0 c ht)

end Mass

theorem actual_source_trace (g : LeptonTrialitySpectrum.PhysicalGroup) :
    LeptonTrialitySpectrum.restricted.character g =
      TorusCharacter.eval LeptonTriality.spectrum (LeptonTrialitySpectrum.coordinateMap g) := by
  have he := LeptonTrialitySpectrum.radical_trace g
  rw [LeptonTrialitySpectrum.restrictedMass_eq_zero,
    Representation.char_iso (SymmetricMass.zeroRadicalEquiv LeptonTrialitySpectrum.restricted)] at he
  exact he

variable {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × Residual) E)

/-- Character matching with the actual 45-dimensional source is sufficient.
The physical covering coordinates are surjective onto the chosen torus. -/
theorem no_conjugations_of_actual_source_character
    (hc : ∀ z h, (restrict j rho).character (PhysicalTorus.toTorus z, h) =
      LeptonTrialitySpectrum.restricted.character (z, h)) :
    ¬ Nonempty (ThreeConjugations j) := by
  have he (g : TorusCharacter.CombinedGroup Residual) :
      (restrict j rho).character g = TorusCharacter.eval LeptonTriality.spectrum g := by
    rcases g with ⟨t, h⟩
    obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
    rw [hc, actual_source_trace]
    rfl
  apply no_conjugations_of_dual_target j rho
  intro g
  rw [Representation.char_dual, he, he, TorusCharacter.eval_chiralDifference]

/-- In particular, no ambient extension on the same fields can preserve the
actual SM-torus/residual action and possess all three geometric witnesses. -/
theorem no_actual_extension (rho' : Representation ℂ (G × Residual) LeptonTrialitySource.HilbertMatter)
    (ha : ∀ z h, (restrict j rho') (PhysicalTorus.toTorus z, h) =
      LeptonTrialitySpectrum.restricted (z, h)) :
    ¬ Nonempty (ThreeConjugations j) := by
  apply no_conjugations_of_actual_source_character j rho'
  intro z h
  change LinearMap.trace ℂ _ ((restrict j rho') (PhysicalTorus.toTorus z, h)) = _
  rw [ha]
  rfl

end
end GUT.StructuralConjugationTriality
