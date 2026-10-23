import Physics.StandardModel.Spectrum.Representations.NonabelianSMTarget
import Physics.StandardModel.Spectrum.Representations.SMPartialTarget
import Physics.StandardModel.Spectrum.Mass.RestrictedConjugationMassSource
import Math.RepresentationTheory.Characters.ResidualAbelianRecovery

open Math

/-!
# Recovery of the existing charge-resolved SM target

On the common unitary Abelian domain, representation-valued local targets
are equivalent to the old coefficientwise `MatchesSM`, for actual spectra
and the charge profiles of actual targets. No finiteness of H is needed here.
-/

set_option autoImplicit false

namespace Physics.NonabelianAbelianRecovery

noncomputable section

open SU5.MaximalTorus SU5.TorusCharacter StandardAbelianCharge
open FiniteAbelianChargeSectors StandardWeylDualTarget StandardSMCharacterTarget
open UnitaryCharacterProfile ResidualAbelianRecovery NonabelianSMTarget

variable {H V : Type*} [CommGroup H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (light : Representation ℂ (Torus × H) V)
  (hl : UnitaryMultiplicity.IsUnitaryRepresentation light)

def actualSpectrum : ResolvedCharacter (ChargeLabel H) :=
  Finsupp.comapDomain keyCharacter (UnitaryCharacterSpectrum.spectrum light hl)
    keyCharacter_injective.injOn

theorem keyCharacter_joint (w : ReducedWeight) (q : ChargeLabel H) :
    keyCharacter (w, q) = UnitaryCharacterSpectrum.complexCharacter
      (jointCharacter (weightCharacter w) q.toMul) := by
  ext g
  rfl

theorem actualSpectrum_apply (w : ReducedWeight) (q : ChargeLabel H) :
    actualSpectrum light hl (w, q) =
      (profile light hl (jointCharacter (weightCharacter w) q.toMul) : ℤ) := by
  rw [actualSpectrum, Finsupp.comapDomain_apply, keyCharacter_joint,
    UnitaryCharacterSpectrum.spectrum_apply_complexCharacter]

theorem actualSpectrum_neg_apply (w : ReducedWeight) (q : ChargeLabel H) :
    actualSpectrum light hl (-(w, q)) =
      (profile light hl (jointCharacter (weightCharacter w)⁻¹ q.toMul⁻¹) : ℤ) := by
  rw [actualSpectrum, Finsupp.comapDomain_apply, ← keyCharacter_neg, keyCharacter_joint]
  have he : AbelianActualSpectrum.dualCharacter
      (UnitaryCharacterSpectrum.complexCharacter (jointCharacter (weightCharacter w) q.toMul)) =
      UnitaryCharacterSpectrum.complexCharacter
        (jointCharacter (weightCharacter w)⁻¹ q.toMul⁻¹) := by
    ext g
    simp [AbelianActualSpectrum.dualCharacter, UnitaryCharacterSpectrum.complexCharacter,
      jointCharacter]
  rw [he, UnitaryCharacterSpectrum.spectrum_apply_complexCharacter]

variable {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)]
  [∀ s, InnerProductSpace ℂ (F s)] [∀ s, FiniteDimensional ℂ (F s)]
  (P : ∀ s, Representation ℂ H (F s))
  (hp : ∀ s, UnitaryMultiplicity.IsUnitaryRepresentation (P s))

def speciesProfile (s : Fin 5) : ChargeLabel H →₀ ℕ :=
  Finsupp.comapDomain Additive.toMul (profile (P s) (hp s)) Additive.toMul.injective.injOn

def targetProfiles : FiniteChargeProfiles.Profiles (ChargeLabel H) :=
  ⟨speciesProfile P hp 0, speciesProfile P hp 1, speciesProfile P hp 2,
    speciesProfile P hp 3, speciesProfile P hp 4⟩

theorem targetProfiles_apply (i : Fin 15) (q : ChargeLabel H) :
    smCharge (targetProfiles P hp) i q = (profile (P (species i)) (hp (species i))) q.toMul := by
  fin_cases i <;> rfl

theorem speciesProfile_total (s : Fin 5) :
    FiniteChargeProfiles.total (speciesProfile P hp s) = Module.finrank ℂ (F s) := by
  unfold FiniteChargeProfiles.total speciesProfile
  have he := Finsupp.sum_comapDomain Additive.toMul (profile (P s) (hp s))
    (fun _ n => n) Additive.toMul.bijective.bijOn_preimage
  exact he.trans (UnitaryCharacterProfile.total_profile (P s) (hp s))

theorem speciesProfile_positive_iff (s : Fin 5) :
    0 < FiniteChargeProfiles.total (speciesProfile P hp s) ↔ Nontrivial (F s) := by
  rw [speciesProfile_total]
  exact Module.finrank_pos_iff

theorem matches_iff_matchesSM :
    Matches light P ↔ SMPartialTarget.MatchesSM (actualSpectrum light hl) (targetProfiles P hp) := by
  have he (i : Fin 15) := index_eq_iff_joint_multiplicities light hl
    (P (species i)) (hp (species i)) (weightCharacter (smReducedWeight i))
  constructor
  · intro ht i q
    have h := (he i).mp (ht i) q.toMul
    simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
      actualSpectrum_apply, actualSpectrum_neg_apply, targetProfiles_apply] using h
  · intro ht i
    apply (he i).mpr
    intro psi
    have h := ht i (Additive.ofMul psi)
    simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
      actualSpectrum_apply, actualSpectrum_neg_apply, targetProfiles_apply,
      toMul_ofMul] using h

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The spectrum used in the equivalence is exactly the old mass-source
spectrum, not a newly assumed Laurent polynomial. -/
theorem actualSpectrum_radical (j : Torus →* G) (rho : Representation ℂ (G × H) E)
    (B : InvariantWeylMass.SymmetricMass (StructuralConjugation.restrict j rho))
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation (StructuralConjugation.restrict j rho)) :
    actualSpectrum B.radical.toRepresentation (Physics.AbelianMassSpectrum.radical_unitary B hu) =
      StructuralConjugationMass.RestrictedUnitary.spectrum j rho B hu := rfl

end
end Physics.NonabelianAbelianRecovery
