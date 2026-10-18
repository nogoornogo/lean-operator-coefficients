import Physics.StandardModel.Gauge.LightSMAction
import Math.RepresentationTheory.Multiplicity.CompactMultiplicityIndex

open Math

/-! The two spectrum inputs give common residual quotients on actual SM
multiplicity spaces. No full-SM invariant mass or field decomposition is assumed. -/

namespace GUT.LightSMSpeciesIndex
set_option autoImplicit false
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open ProductFactorization SplitRepresentationProjection
open SU5.MaximalTorus

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)

abbrev quark := multiplicityRepresentation D.action StandardSMGaugeTensor.quark
abbrev up := multiplicityRepresentation D.action StandardSMGaugeTensor.upRight.dual
abbrev electron := multiplicityRepresentation D.action StandardSMGaugeTensor.electronRight.dual

variable {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)]
  [∀ s, NormedSpace ℂ (F s)]
  (P : ∀ s, Representation ℂ H (F s))

/-- Species-resolved indices, additional to the four monitored weight indices. -/
def HasTarget : Prop :=
  (∀ h, CompactMultiplicityIndex.index D.action StandardSMGaugeTensor.quark h =
    (P 0).character h) ∧
  (∀ h, CompactMultiplicityIndex.index D.action StandardSMGaugeTensor.upRight.dual h =
    (P 1).character h) ∧
  (∀ h, CompactMultiplicityIndex.index D.action StandardSMGaugeTensor.electronRight.dual h =
    (P 4).character h)

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [FiniteDimensional ℂ (F 0)] [Nontrivial (F 0)]

theorem common_quotient
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (hs : HasTarget j rho B D P)
    (c : StructuralConjugation.TwoConjugations j) :
    ∃ S : Subrepresentation (P 0), IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧
      Nonempty (Split (quark j rho B D) S.toRepresentation) ∧
      Nonempty (Split (up j rho B D) S.toRepresentation) ∧
      Nonempty (Split (electron j rho B D) S.toRepresentation) := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨h01, h04⟩ := FourWeightLightQque.characters_compatible j rho B hu P ht c
  obtain ⟨S, hi, hn, f, hf⟩ :=
    CompactIrreducibleQuotient.exists_irreducible_quotient (P 0) hp
  let : IsIrreducible S.toRepresentation := hi
  let : Nontrivial S.toSubmodule := hn
  have hfn : f ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
    obtain ⟨y, hy⟩ := hf x
    exact hx (by simpa [he] using hy.symm)
  have hl : IsJointlyContinuous (secondRestriction D.action) :=
    hd.comp (ContinuousMonoidHom.inr _ H)
  refine ⟨S, hi, hn, ?_, ?_, ?_⟩
  · exact CompactMultiplicityIndex.exists_split_of_index_eq D.action
      StandardSMGaugeTensor.quark hl (P 0) hp S.toRepresentation
      (hp.subrepresentation S) hs.1 f hfn
  · exact CompactMultiplicityIndex.exists_split_of_index_eq D.action
      StandardSMGaugeTensor.upRight.dual hl (P 0) hp S.toRepresentation
      (hp.subrepresentation S) (fun h => (hs.2.1 h).trans (congrFun h01.symm h)) f hfn
  · exact CompactMultiplicityIndex.exists_split_of_index_eq D.action
      StandardSMGaugeTensor.electronRight.dual hl (P 0) hp S.toRepresentation
      (hp.subrepresentation S) (fun h => (hs.2.2 h).trans (congrFun h04.symm h)) f hfn

end
end GUT.LightSMSpeciesIndex
