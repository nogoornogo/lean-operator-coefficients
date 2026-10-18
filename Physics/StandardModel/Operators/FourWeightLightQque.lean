import Physics.StandardModel.Operators.NonabelianLightOperators
import Physics.StandardModel.Spectrum.QqueLocalTarget

open Math

/-! Finite non-Abelian internal qque coefficients from four monitored weights. -/

set_option autoImplicit false
namespace GUT.FourWeightLightQque
noncomputable section

open Representation NonabelianSMTarget NonabelianLightSource NonabelianLightOperators
open SU5.MaximalTorus StandardSMCharacterTarget StandardAbelianCharge
open StructuralConjugation InvariantWeylMass ResidualWeightSpace ResidualWeightCharacter
open SplitRepresentationProjection QqueLocalTarget

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Fin 5 → Type*} [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))
  (P : ∀ s, Representation ℂ H (F s))

def HasTarget : Prop := ∀ i : Fin 15, Monitored i → ∀ h : H,
  index B.radical.toRepresentation (SU5.TorusCharacter.weightCharacter (smReducedWeight i)) h =
    (P (species i)).character h

omit [FiniteDimensional ℂ E] in
theorem of_matches (ht : NonabelianSMTarget.Matches B.radical.toRepresentation P) :
    HasTarget j rho B P := fun i _ h => ht i h

omit [FiniteDimensional ℂ E] in
/-- Unused down/lepton targets do not constrain the four-weight condition. -/
theorem target_iff_of_characters_eq (R : ∀ s, Representation ℂ H (F s))
    (hq : (P 0).character = (R 0).character)
    (hu' : (P 1).character = (R 1).character)
    (he : (P 4).character = (R 4).character) :
    HasTarget j rho B P ↔ HasTarget j rho B R := by
  have hm (i : Fin 15) (hi : Monitored i) :
      (P (species i)).character = (R (species i)).character := by
    rcases hi with rfl | rfl | rfl | rfl
    · exact hq
    · exact hq
    · exact hu'
    · exact he
  constructor <;> intro h i hi x
  · rw [← hm i hi]; exact h i hi x
  · rw [hm i hi]; exact h i hi x

include hu in
theorem characters_compatible (ht : HasTarget j rho B P) (c : TwoConjugations j) :
    (P 0).character = (P 1).character ∧ (P 0).character = (P 4).character := by
  have h01 : permuteReducedWeight (Equiv.swap (3 : Fin 5) 1) (smReducedWeight 0) =
      smReducedWeight 8 := by
    rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl,
      (smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl]
    exact permuteReducedWeight_swap31_tenQ
  have h04 : permuteReducedWeight (Equiv.swap (0 : Fin 5) 4) (smReducedWeight 0) =
      smReducedWeight 14 := by
    rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl,
      (smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl]
    exact permuteReducedWeight_swap04_tenQ
  constructor
  · funext h
    have he := index_permute j rho B hu _ c.quarkUp (smReducedWeight 0) h
    rw [h01] at he
    exact (ht 0 (Or.inl rfl) h).symm.trans
      (he.symm.trans (ht 8 (Or.inr (Or.inr (Or.inl rfl))) h))
  · funext h
    have he := index_permute j rho B hu _ c.quarkElectron (smReducedWeight 0) h
    rw [h04] at he
    exact (ht 0 (Or.inl rfl) h).symm.trans
      (he.symm.trans (ht 14 (Or.inr (Or.inr (Or.inr rfl))) h))

variable [Fintype H] [∀ s, FiniteDimensional ℂ (F s)]

include hu in
theorem common_quotient [Nontrivial (F 0)] (ht : HasTarget j rho B P)
    (c : TwoConjugations j) :
    ∃ S : Subrepresentation (P 0), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i : Fin 15, Monitored i →
        Nonempty (Split (lightSector j rho B i) S.toRepresentation) := by
  obtain ⟨h01, h04⟩ := characters_compatible j rho B hu P ht c
  obtain ⟨S, hi, hn, hs⟩ :=
    ResidualLightQuotient.exists_common_quotient B.radical.toRepresentation (P 0)
  refine ⟨S, hi, hn, fun i hi => hs _ ?_⟩
  intro h
  rw [ht i hi h]
  rcases hi with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact congrFun h01.symm h
  · exact congrFun h04.symm h

include hu in
set_option maxHeartbeats 4000000 in
theorem exists_qque_coefficient [Nontrivial (F 0)]
    (ht : HasTarget j rho B P) (c : TwoConjugations j) :
    ∃ f : IntertwiningMap (qqueRepresentation j rho B 0 3 8 14)
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨S, _, hn, hs⟩ := common_quotient (F := F) j rho B hu P ht c
  let : Nontrivial S.toSubmodule := hn
  obtain ⟨sq₁⟩ := hs 0 (Or.inl rfl)
  obtain ⟨sq₂⟩ := hs 3 (Or.inr (Or.inl rfl))
  obtain ⟨su⟩ := hs 8 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨se⟩ := hs 14 (Or.inr (Or.inr (Or.inr rfl)))
  exact OrderedInvariantPairing.exists_ordered_coefficient sq₁ su sq₂ se

include hu in
theorem not_forbidsBothInternalCoefficients [Nontrivial (F 0)]
    (ht : HasTarget j rho B P) (c : TwoConjugations j) :
    ¬ ForbidsBothInternalCoefficients j rho B := by
  intro h
  obtain ⟨f, hf⟩ := exists_qque_coefficient j rho B hu P ht c
  exact hf (h.1 f)

end
end GUT.FourWeightLightQque
