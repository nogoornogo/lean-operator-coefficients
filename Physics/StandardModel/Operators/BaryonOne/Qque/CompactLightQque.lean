import Physics.StandardModel.Operators.BaryonOne.Qque.FourWeightLightQque
import Physics.FieldTheory.Mass.Algebra.CompactResidualLightQuotient

open Math

/-! Four-weight qque coefficients for compact continuous residual groups.
Only the residual action is assumed continuous, not the ambient gauge group.
The original mass radical and its torus-weight spaces are retained. -/

namespace Physics.CompactLightQque
noncomputable section

open Representation NonabelianSMTarget NonabelianLightSource NonabelianLightOperators
open SU5.MaximalTorus StandardSMCharacterTarget StandardAbelianCharge
open StructuralConjugation InvariantWeylMass ResidualWeightSpace ResidualWeightCharacter
open SplitRepresentationProjection QqueLocalTarget ContinuousRepresentationScope

variable {H G E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℂ (F s)]
  [FiniteDimensional ℂ (F 0)]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation
    (torus (rho.comp (j.prodMap (MonoidHom.id H)))))
  (P : ∀ s, Representation ℂ H (F s))

omit [CompactSpace H] [IsTopologicalGroup H] [FiniteDimensional ℂ E] in
theorem radical_residual_continuous
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H))) :
    IsJointlyContinuous (residual B.radical.toRepresentation) := by
  apply ResidualWeightContinuity.subrepresentation _ B.radical
  have he : residual (rho.comp (j.prodMap (MonoidHom.id H))) =
      rho.comp (MonoidHom.inr G H) := by
    ext h v
    simp [ResidualWeightSpace.residual]
  rw [he]
  exact hr

include hu in
/-- The common irreducible constituent and all four split projections are
derived, not additional source certificates. -/
theorem common_quotient [Nontrivial (F 0)]
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H)))
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P) (c : TwoConjugations j) :
    ∃ S : Subrepresentation (P 0), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i : Fin 15, Monitored i →
        Nonempty (Split (lightSector j rho B i) S.toRepresentation) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨h01, h04⟩ := FourWeightLightQque.characters_compatible j rho B hu P ht c
  obtain ⟨S, hi, hn, hs⟩ :=
    CompactResidualLightQuotient.exists_common_quotient B.radical.toRepresentation
      (radical_residual_continuous j rho B hr) (P 0) hp
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
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H)))
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P) (c : TwoConjugations j) :
    ∃ f : IntertwiningMap (qqueRepresentation j rho B 0 3 8 14)
      (Representation.trivial ℂ H ℂ), f ≠ 0 := by
  obtain ⟨S, _, hn, hs⟩ := common_quotient j rho B hu P hr hp ht c
  let : Nontrivial S.toSubmodule := hn
  obtain ⟨sq₁⟩ := hs 0 (Or.inl rfl)
  obtain ⟨sq₂⟩ := hs 3 (Or.inr (Or.inl rfl))
  obtain ⟨su⟩ := hs 8 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨se⟩ := hs 14 (Or.inr (Or.inr (Or.inr rfl)))
  exact OrderedInvariantPairing.exists_ordered_coefficient sq₁ su sq₂ se

include hu in
theorem not_forbidsBothInternalCoefficients [Nontrivial (F 0)]
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H)))
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P) (c : TwoConjugations j) :
    ¬ ForbidsBothInternalCoefficients j rho B := by
  intro h
  obtain ⟨f, hf⟩ := exists_qque_coefficient j rho B hu P hr hp ht c
  exact hf (h.1 f)

end
end Physics.CompactLightQque
