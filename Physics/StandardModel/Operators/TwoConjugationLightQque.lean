import Physics.StandardModel.Operators.NonabelianLightOperators

open Math

/-! Two actual conjugations suffice for the finite non-Abelian light qque
internal coefficient, without down/lepton positivity. With positive down
target the same moves also recover duql via the other monitored weights. -/

set_option autoImplicit false
namespace GUT.TwoConjugationLightQque
noncomputable section

open Representation NonabelianSMTarget NonabelianLightSource NonabelianLightOperators
open SU5.MaximalTorus StandardSMCharacterTarget StandardAbelianCharge
open StructuralConjugation InvariantWeylMass ResidualWeightSpace SplitRepresentationProjection

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Fin 5 → Type*} [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))
  (P : ∀ s, Representation ℂ H (F s))
  (ht : Matches B.radical.toRepresentation P) (c : TwoConjugations j)

include hu ht c in
theorem characters_compatible :
    (P 0).character = (P 1).character ∧ (P 0).character = (P 4).character := by
  constructor
  · apply target_character_eq j rho B hu P ht 0 8 _ c.quarkUp
    rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl,
      (smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl]
    exact permuteReducedWeight_swap31_tenQ
  · apply target_character_eq j rho B hu P ht 0 14 _ c.quarkElectron
    rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl,
      (smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl]
    exact permuteReducedWeight_swap04_tenQ

include hu ht c in
theorem down_lepton_character_eq : (P 2).character = (P 3).character := by
  apply target_character_eq j rho B hu P ht 10 13 _ c.quarkUp
  exact swap31_down_lepton

variable [Fintype H] [∀ s, FiniteDimensional ℂ (F s)]

include hu ht c in
theorem common_quotient [Nontrivial (F 0)] :
    ∃ S : Subrepresentation (P 0), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i : Fin 15,
        (species i = 0 ∨ species i = 1 ∨ species i = 4) →
          Nonempty (Split (lightSector j rho B i) S.toRepresentation) := by
  obtain ⟨h01, h04⟩ := characters_compatible j rho B hu P ht c
  obtain ⟨S, hi, hn, hs⟩ :=
    ResidualLightQuotient.exists_common_quotient B.radical.toRepresentation (P 0)
  refine ⟨S, hi, hn, fun i h => hs _ ?_⟩
  intro x
  rw [ht i x]
  rcases h with h | h | h
  · rw [h]
  · rw [h, h01]
  · rw [h, h04]

include hu ht c in
theorem common_barFive_quotient [Nontrivial (F 2)] :
    ∃ S : Subrepresentation (P 2), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i : Fin 15,
        (species i = 2 ∨ species i = 3) →
          Nonempty (Split (lightSector j rho B i) S.toRepresentation) := by
  have h23 := down_lepton_character_eq j rho B hu P ht c
  obtain ⟨S, hi, hn, hs⟩ :=
    ResidualLightQuotient.exists_common_quotient B.radical.toRepresentation (P 2)
  refine ⟨S, hi, hn, fun i h => hs _ ?_⟩
  intro x
  rw [ht i x]
  rcases h with h | h
  · rw [h]
  · rw [h, h23]

include hu ht c in
-- As in the three-conjugation endpoint, nested actual sector types need a local budget.
set_option maxHeartbeats 4000000 in
theorem exists_qque_coefficient [Nontrivial (F 0)]
    (q₁ q₂ u e : Fin 15) (hq₁ : species q₁ = 0) (hq₂ : species q₂ = 0)
    (hu' : species u = 1) (he : species e = 4) :
    ∃ f : IntertwiningMap (qqueRepresentation j rho B q₁ q₂ u e)
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨S, _, hn, hs⟩ := common_quotient (F := F) j rho B hu P ht c
  let : Nontrivial S.toSubmodule := hn
  obtain ⟨sq₁⟩ := hs q₁ (Or.inl hq₁)
  obtain ⟨sq₂⟩ := hs q₂ (Or.inl hq₂)
  obtain ⟨su⟩ := hs u (Or.inr (Or.inl hu'))
  obtain ⟨se⟩ := hs e (Or.inr (Or.inr he))
  exact OrderedInvariantPairing.exists_ordered_coefficient sq₁ su sq₂ se

include hu ht c in
theorem not_forbidsBothInternalCoefficients [Nontrivial (F 0)] :
    ¬ ForbidsBothInternalCoefficients j rho B := by
  intro h
  obtain ⟨f, hf⟩ := exists_qque_coefficient j rho B hu P ht c 0 3 8 14 rfl rfl rfl rfl
  exact hf (h.1 f)

include hu ht c in
set_option maxHeartbeats 12000000 in
theorem exists_duql_coefficient [Nontrivial (F 0)] [Nontrivial (F 2)]
    (d u q l : Fin 15) (hd : species d = 2) (hu' : species u = 1)
    (hq : species q = 0) (hl : species l = 3) :
    ∃ f : IntertwiningMap (duqlRepresentation j rho B d u q l)
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨S, _, hn, hs⟩ := common_quotient (F := F) j rho B hu P ht c
  obtain ⟨T, _, hm, ht'⟩ := common_barFive_quotient (F := F) j rho B hu P ht c
  let : Nontrivial S.toSubmodule := hn
  let : Nontrivial T.toSubmodule := hm
  obtain ⟨sq⟩ := hs q (Or.inl hq)
  obtain ⟨su⟩ := hs u (Or.inr (Or.inl hu'))
  obtain ⟨sd⟩ := ht' d (Or.inl hd)
  obtain ⟨sl⟩ := ht' l (Or.inr hl)
  exact OrderedInvariantPairing.exists_dual_first_coefficient sq su sl sd

include hu ht c in
theorem both_coefficients_exist [Nontrivial (F 0)] [Nontrivial (F 2)] :
    (∃ f : IntertwiningMap (qqueRepresentation j rho B 0 3 8 14)
      (Representation.trivial ℂ H ℂ), f ≠ 0) ∧
    (∃ f : IntertwiningMap (duqlRepresentation j rho B 9 8 2 13)
      (Representation.trivial ℂ H ℂ), f ≠ 0) := by
  constructor
  · exact exists_qque_coefficient j rho B hu P ht c 0 3 8 14 rfl rfl rfl rfl
  · exact exists_duql_coefficient j rho B hu P ht c 9 8 2 13 rfl rfl rfl rfl

end
end GUT.TwoConjugationLightQque
