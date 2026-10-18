import Physics.StandardModel.Spectrum.LightSMSpeciesIndex
import Math.RepresentationTheory.Multiplicity.CompactVirtualMultiplicityIndex

open Math

/-! Virtual species targets: actual conjugation relates signed characters,
and positive total dimension replaces an everywhere-positive actual target. -/

namespace GUT.VirtualSMSpeciesIndex
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open ProductFactorization SplitRepresentationProjection
open SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardSMCharacterTarget StandardAbelianCharge NonabelianSMTarget

variable {H G E I : Type*} [Group H] [Group G] [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (S : ∀ i, Representation ℂ H (V i)) (a : Fin 5 → I → ℤ)

def WeightMatches : Prop := ∀ k : Fin 15, QqueLocalTarget.Monitored k → ∀ h,
  ResidualWeightCharacter.index B.radical.toRepresentation (weightCharacter (smReducedWeight k)) h =
    CompactVirtualCharacter.character S (a (species k)) h

def SpeciesMatches : Prop :=
  (∀ h, CompactMultiplicityIndex.index D.action StandardSMGaugeTensor.quark h =
    CompactVirtualCharacter.character S (a 0) h) ∧
  (∀ h, CompactMultiplicityIndex.index D.action StandardSMGaugeTensor.upRight.dual h =
    CompactVirtualCharacter.character S (a 1) h) ∧
  (∀ h, CompactMultiplicityIndex.index D.action StandardSMGaugeTensor.electronRight.dual h =
    CompactVirtualCharacter.character S (a 4) h)

omit [∀ i, FiniteDimensional ℂ (V i)] in
theorem characters_compatible
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (ht : WeightMatches j rho B S a) (c : TwoConjugations j) :
    CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 1) ∧
    CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 4) := by
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

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [∀ i, IsIrreducible (S i)]
  (hc : ∀ i, IsJointlyContinuous (S i))
  (hn : ∀ i k, i ≠ k → IsEmpty (Representation.Equiv (S i) (S k)))

include hc hn in
theorem common_quotient
    (hd : IsJointlyContinuous D.action)
    (hs : SpeciesMatches j rho B D S a)
    (he : CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 1) ∧
      CompactVirtualCharacter.character S (a 0) = CompactVirtualCharacter.character S (a 4))
    (hp : 0 < CompactVirtualCharacter.dimension (V := V) (a 0)) :
    ∃ i, Nontrivial (V i) ∧
      Nonempty (Split (LightSMSpeciesIndex.quark j rho B D) (S i)) ∧
      Nonempty (Split (LightSMSpeciesIndex.up j rho B D) (S i)) ∧
      Nonempty (Split (LightSMSpeciesIndex.electron j rho B D) (S i)) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨i, hi, hv⟩ := CompactVirtualCharacter.exists_positive (a 0) hp
  have hl : IsJointlyContinuous (secondRestriction D.action) :=
    hd.comp (ContinuousMonoidHom.inr _ H)
  refine ⟨i, Module.finrank_pos_iff.mp hv, ?_, ?_, ?_⟩
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 0) hc hn D.action
      StandardSMGaugeTensor.quark hl hs.1 i hi
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 0) hc hn D.action
      StandardSMGaugeTensor.upRight.dual hl
      (fun h => (hs.2.1 h).trans (congrFun he.1.symm h)) i hi
  · exact CompactVirtualMultiplicityIndex.exists_split S (a 0) hc hn D.action
      StandardSMGaugeTensor.electronRight.dual hl
      (fun h => (hs.2.2 h).trans (congrFun he.2.symm h)) i hi

end
end GUT.VirtualSMSpeciesIndex
