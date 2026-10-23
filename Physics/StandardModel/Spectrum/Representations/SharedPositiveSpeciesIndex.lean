import Physics.StandardModel.Spectrum.Representations.VirtualSMSpeciesIndex

open Math

/-! One common positive constituent suffices; the remaining signed species
coefficients need not agree, and their total dimensions need not be positive. -/

namespace Physics.SharedPositiveSpeciesIndex
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open ProductFactorization SplitRepresentationProjection SU5.MaximalTorus

def SharedPositive {I : Type*} (a : Fin 5 → I → ℤ) : Prop :=
  ∃ i, 0 < a 0 i ∧ 0 < a 1 i ∧ 0 < a 4 i

variable {H I : Type*} [Group H] [Fintype I]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (S : ∀ i, Representation ℂ H (V i)) [∀ i, IsIrreducible (S i)]
  (a : Fin 5 → I → ℤ) (hc : ∀ i, IsJointlyContinuous (S i))
  (hn : ∀ i k, i ≠ k → IsEmpty (Representation.Equiv (S i) (S k)))

include hc hn in
theorem of_common_index
    (he : CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 1) ∧
      CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 4))
    (hp : 0 < CompactVirtualCharacter.dimension (V := V) (a 0)) : SharedPositive a := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨i, hi, _⟩ := CompactVirtualCharacter.exists_positive (a 0) hp
  have hu := CompactVirtualCharacter.character_injective S hc hn he.1
  have he' := CompactVirtualCharacter.character_injective S hc hn he.2
  exact ⟨i, hi, hu ▸ hi, he' ▸ hi⟩

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)

include hc hn in
theorem of_conjugations
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (ht : VirtualSMSpeciesIndex.WeightMatches j rho B S a)
    (hp : 0 < CompactVirtualCharacter.dimension (V := V) (a 0))
    (c : StructuralConjugation.TwoConjugations j) : SharedPositive a :=
  of_common_index S a hc hn
    (VirtualSMSpeciesIndex.characters_compatible j rho B S a hu ht c) hp

include hc hn in
theorem common_quotient
    (hd : IsJointlyContinuous D.action)
    (hs : VirtualSMSpeciesIndex.SpeciesMatches j rho B D S a)
    (hp : SharedPositive a) :
    ∃ i, Nontrivial (V i) ∧
      Nonempty (Split (LightSMSpeciesIndex.quark j rho B D) (S i)) ∧
      Nonempty (Split (LightSMSpeciesIndex.up j rho B D) (S i)) ∧
      Nonempty (Split (LightSMSpeciesIndex.electron j rho B D) (S i)) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨i, hq, hu, he⟩ := hp
  have hl : IsJointlyContinuous (secondRestriction D.action) :=
    hd.comp (ContinuousMonoidHom.inr _ H)
  refine ⟨i, IsIrreducible.nontrivial (inferInstance : IsIrreducible (S i)), ?_, ?_, ?_⟩
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 0) hc hn D.action
      StandardSMGaugeTensor.quark hl hs.1 i hq
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 1) hc hn D.action
      StandardSMGaugeTensor.upRight.dual hl hs.2.1 i hu
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 4) hc hn D.action
      StandardSMGaugeTensor.electronRight.dual hl hs.2.2 i he

end
end Physics.SharedPositiveSpeciesIndex
