import Physics.StandardModel.Operators.BaryonOne.Qque.FullLightRadicalQque
import Math.RepresentationTheory.Decomposition.CommonIrreducible
import Math.RepresentationTheory.Decomposition.SymmetricSquareSemisimple
import Math.RepresentationTheory.Multiplicity.CompactMultiplicityIndex

open Math

/-! A complete constituent criterion AFTER forming the symmetric square and
tensor product. These are actual multiplicities, not signed species indices. -/
namespace Physics.QqueCommonIrreducible
noncomputable section
open Representation ProductFactorization ContinuousRepresentationScope
open StandardSMGaugeTensor

section Multiplicities
variable {H A B D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

def Shares : Prop := CommonIrreducible.Shares (a.symmetricPower 2) (b.tprod d)

theorem hom_iff (hs : IsSemisimpleRepresentation (a.symmetricPower 2)) :
    (∃ f : IntertwiningMap (a.symmetricPower 2) (b.tprod d), f ≠ 0) ↔ Shares a b d :=
  CommonIrreducible.nonzero_iff _ _ hs

variable [FiniteDimensional ℂ B] [FiniteDimensional ℂ D]

theorem coefficient_iff (hs : IsSemisimpleRepresentation (a.symmetricPower 2)) :
    (∃ f : QqueCoefficientCompleteness.Sector a b d, f ≠ 0) ↔ Shares a b d := by
  refine Iff.trans ?_ (hom_iff a b d hs)
  let e := QqueCoefficientCompleteness.equiv a b d
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨e.symm f, ?_⟩
    intro hz
    exact hf (e.symm.injective (hz.trans (map_zero e.symm).symm))
  · rintro ⟨f, hf⟩
    refine ⟨e f, ?_⟩
    intro hz
    exact hf (e.injective (hz.trans (map_zero e).symm))
end Multiplicities

section FullFields
variable {H K : Type*} [Group H]
  [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
  (tau : Representation ℂ (GaugeGroup × H) K)

def FullShares : Prop := Shares
  (multiplicityRepresentation tau quark)
  (multiplicityRepresentation tau upRight.dual)
  (multiplicityRepresentation tau electronRight.dual)

theorem full_nonzero_iff (hs : IsSemisimpleRepresentation (firstRestriction tau))
    (hq : IsSemisimpleRepresentation ((multiplicityRepresentation tau quark).symmetricPower 2)) :
    FullLightSpeciesQque.HasCoefficient tau ↔ FullShares tau :=
  (FullLightSpeciesQque.nonzero_iff tau hs).trans (hom_iff _ _ _ hq)

theorem full_forbidden_iff (hs : IsSemisimpleRepresentation (firstRestriction tau))
    (hq : IsSemisimpleRepresentation ((multiplicityRepresentation tau quark).symmetricPower 2)) :
    ¬ FullLightSpeciesQque.HasCoefficient tau ↔ ¬ FullShares tau :=
  not_congr (full_nonzero_iff tau hs hq)
end FullFields

section Compact
variable {H A B D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
  [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

/-- Only Q continuity is needed to make the source symmetric square semisimple. -/
theorem coefficient_iff_of_compact (ha : IsJointlyContinuous a) :
    (∃ f : QqueCoefficientCompleteness.Sector a b d, f ≠ 0) ↔ Shares a b d :=
  coefficient_iff a b d (SymmetricSquareSemisimple.of_compact a ha)
end Compact

section CompactFull
variable {H K : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [NormedAddCommGroup K] [NormedSpace ℂ K] [FiniteDimensional ℂ K]
  (tau : Representation ℂ (GaugeGroup × H) K)

theorem full_square_semisimple (hr : IsJointlyContinuous (secondRestriction tau)) :
    IsSemisimpleRepresentation ((multiplicityRepresentation tau quark).symmetricPower 2) := by
  let := CompactMultiplicityIndex.normedAddCommGroup tau quark
  let := CompactMultiplicityIndex.normedSpace tau quark
  exact SymmetricSquareSemisimple.of_compact (multiplicityRepresentation tau quark)
    (CompactMultiplicityIndex.jointlyContinuous tau quark hr)

theorem full_nonzero_iff_of_compact
    (hs : IsSemisimpleRepresentation (firstRestriction tau))
    (hr : IsJointlyContinuous (secondRestriction tau)) :
    FullLightSpeciesQque.HasCoefficient tau ↔ FullShares tau :=
  full_nonzero_iff tau hs (full_square_semisimple tau hr)
end CompactFull

section Radical
open InvariantWeylMass
variable {H G V : Type*} [Group H] [Group G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) V)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)

theorem radical_nonzero_iff (hd : IsJointlyContinuous D.action) :
    FullLightSpeciesQque.HasCoefficient D.action ↔ FullShares D.action :=
  full_nonzero_iff_of_compact D.action
    (FullLightRadicalQque.sm_semisimple j rho B D
      (hd.comp (ContinuousMonoidHom.inl GaugeGroup H)))
    (hd.comp (ContinuousMonoidHom.inr GaugeGroup H))

theorem radical_forbidden_iff (hd : IsJointlyContinuous D.action) :
    ¬ FullLightSpeciesQque.HasCoefficient D.action ↔ ¬ FullShares D.action :=
  not_congr (radical_nonzero_iff j rho B D hd)
end Radical

end
end Physics.QqueCommonIrreducible
