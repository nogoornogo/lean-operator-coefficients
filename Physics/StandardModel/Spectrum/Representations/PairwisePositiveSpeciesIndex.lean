import Physics.StandardModel.Spectrum.Representations.SharedPositiveSpeciesIndex

open Math

namespace Physics.PairwisePositiveSpeciesIndex
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open ProductFactorization SplitRepresentationProjection SU5.MaximalTorus

def PairwisePositive {I : Type*} (a : Fin 5 → I → ℤ) : Prop :=
  ∃ i k, (0 < a 0 i ∧ 0 < a 1 i) ∧ (0 < a 0 k ∧ 0 < a 4 k)

theorem of_shared {I : Type*} {a : Fin 5 → I → ℤ}
    (hp : SharedPositiveSpeciesIndex.SharedPositive a) : PairwisePositive a := by
  obtain ⟨i, hq, hu, he⟩ := hp
  exact ⟨i, i, ⟨hq, hu⟩, ⟨hq, he⟩⟩

variable {H I : Type*} [Group H] [Fintype I]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (S : ∀ i, Representation ℂ H (V i)) [∀ i, IsIrreducible (S i)]
  (a : Fin 5 → I → ℤ) (hc : ∀ i, IsJointlyContinuous (S i))
  (hn : ∀ i k, i ≠ k → IsEmpty (Representation.Equiv (S i) (S k)))
  {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)

include hc hn in
theorem pairwise_quotients
    (hd : IsJointlyContinuous D.action)
    (hs : VirtualSMSpeciesIndex.SpeciesMatches j rho B D S a)
    (hp : PairwisePositive a) :
    ∃ i k, Nontrivial (V i) ∧ Nontrivial (V k) ∧
      Nonempty (Split (LightSMSpeciesIndex.quark j rho B D) (S i)) ∧
      Nonempty (Split (LightSMSpeciesIndex.up j rho B D) (S i)) ∧
      Nonempty (Split (LightSMSpeciesIndex.quark j rho B D) (S k)) ∧
      Nonempty (Split (LightSMSpeciesIndex.electron j rho B D) (S k)) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨i, k, ⟨hq, hu⟩, ⟨hq', he⟩⟩ := hp
  have hl : IsJointlyContinuous (secondRestriction D.action) :=
    hd.comp (ContinuousMonoidHom.inr _ H)
  refine ⟨i, k, IsIrreducible.nontrivial (inferInstance : IsIrreducible (S i)),
    IsIrreducible.nontrivial (inferInstance : IsIrreducible (S k)), ?_, ?_, ?_, ?_⟩
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 0) hc hn D.action
      StandardSMGaugeTensor.quark hl hs.1 i hq
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 1) hc hn D.action
      StandardSMGaugeTensor.upRight.dual hl hs.2.1 i hu
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 0) hc hn D.action
      StandardSMGaugeTensor.quark hl hs.1 k hq'
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 4) hc hn D.action
      StandardSMGaugeTensor.electronRight.dual hl hs.2.2 k he

end
end Physics.PairwisePositiveSpeciesIndex
