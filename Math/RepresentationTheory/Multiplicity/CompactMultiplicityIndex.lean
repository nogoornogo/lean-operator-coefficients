import Math.RepresentationTheory.Decomposition.ProductFactorization
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient
import Math.RepresentationTheory.Unitary.ContinuousDual
import Math.RepresentationTheory.Characters.CompactPositiveCharacterQuotient

/-! Continuous residual multiplicities and positive species indices.
Auxiliary norms are on the original algebraic Hom spaces, not new source data. -/

namespace Math.CompactMultiplicityIndex
noncomputable section
open Representation ProductFactorization ContinuousRepresentationScope
open SplitRepresentationProjection

variable {G H E U : Type*} [Group G] [Group H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (tau : Representation ℂ (G × H) E) (r : Representation ℂ G U)

def coordinates := (Module.finBasis ℂ (MultiplicitySpace tau r)).equivFun

@[instance_reducible]
def normedAddCommGroup : NormedAddCommGroup (MultiplicitySpace tau r) :=
  NormedAddCommGroup.induced _ _ (coordinates tau r).toAddEquiv.toAddMonoidHom
    (coordinates tau r).injective

@[instance_reducible]
def normedSpace : letI := normedAddCommGroup tau r
    NormedSpace ℂ (MultiplicitySpace tau r) := by
  letI := normedAddCommGroup tau r
  exact NormedSpace.induced ℂ _ _ (coordinates tau r).toLinearMap

def basisEvaluation : MultiplicitySpace tau r →ₗ[ℂ]
    (Fin (Module.finrank ℂ U) → E) where
  toFun f i := f (Module.finBasis ℂ U i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℂ E] in
theorem basisEvaluation_injective : Function.Injective (basisEvaluation tau r) := by
  intro f g he
  apply IntertwiningMap.ext
  apply (Module.finBasis ℂ U).ext
  intro i
  exact congrFun he i

variable [TopologicalSpace H]

theorem jointlyContinuous
    (ht : IsJointlyContinuous (secondRestriction tau)) :
    letI := normedAddCommGroup tau r
    letI := normedSpace tau r
    IsJointlyContinuous (multiplicityRepresentation tau r) := by
  let := normedAddCommGroup tau r
  let := normedSpace tau r
  change Continuous (fun p : H × MultiplicitySpace tau r =>
    multiplicityRepresentation tau r p.1 p.2)
  apply (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (basisEvaluation_injective tau r))).isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro i
  exact Continuous.comp ht (continuous_fst.prodMk
    ((continuous_apply i).comp
      ((basisEvaluation tau r).continuous_of_finiteDimensional.comp continuous_snd)))

def index (h : H) : ℂ :=
  (multiplicityRepresentation tau r).character h -
    (multiplicityRepresentation tau r.dual).dual.character h

variable [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {P W : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem exists_split_of_index_eq
    (ht : IsJointlyContinuous (secondRestriction tau))
    (target : Representation ℂ H P) (hp : IsJointlyContinuous target)
    (w : Representation ℂ H W) [IsIrreducible w] (hw : IsJointlyContinuous w)
    (hi : ∀ h, index tau r h = target.character h)
    (f : IntertwiningMap target w) (hf : f ≠ 0) :
    Nonempty (Split (multiplicityRepresentation tau r) w) := by
  let := normedAddCommGroup tau r
  let := normedSpace tau r
  let := normedAddCommGroup tau r.dual
  let := normedSpace tau r.dual
  let := ContinuousDual.dualNormedAddCommGroup (V := MultiplicitySpace tau r.dual)
  let := ContinuousDual.dualNormedSpace (V := MultiplicitySpace tau r.dual)
  have hr := jointlyContinuous tau r ht
  have hd := ContinuousDual.jointlyContinuous_dual
    (multiplicityRepresentation tau r.dual) (jointlyContinuous tau r.dual ht)
  have he : ∀ h, (multiplicityRepresentation tau r).character h =
      (multiplicityRepresentation tau r.dual).dual.character h + target.character h := by
    intro h
    have hh := hi h
    unfold index at hh
    linear_combination hh
  obtain ⟨p, hs⟩ :=
    CompactPositiveCharacterQuotient.exists_surjective_of_character_add_of_nonzero
      (multiplicityRepresentation tau r) (multiplicityRepresentation tau r.dual).dual
      target w hr hd hp hw he f hf
  obtain ⟨s, _⟩ := SemisimpleSplitting.exists_split _ _
    (CompactIrreducibleQuotient.semisimple _ hr) p hs
  exact ⟨s⟩

theorem exists_common_quotient
    {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (r : ∀ i, Representation ℂ G (V i))
    (ht : IsJointlyContinuous (secondRestriction tau))
    (target : Representation ℂ H P) (hp : IsJointlyContinuous target) [Nontrivial P]
    (hi : ∀ i h, index tau (r i) h = target.character h) :
    ∃ S : Subrepresentation target, IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ i,
        Nonempty (Split (multiplicityRepresentation tau (r i)) S.toRepresentation) := by
  obtain ⟨S, hirr, hn, f, hsurj⟩ :=
    CompactIrreducibleQuotient.exists_irreducible_quotient target hp
  let : IsIrreducible S.toRepresentation := hirr
  let : Nontrivial S.toSubmodule := hn
  have hf : f ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
    obtain ⟨y, hy⟩ := hsurj x
    exact hx (by simpa [he] using hy.symm)
  exact ⟨S, hirr, hn, fun i => exists_split_of_index_eq tau (r i) ht target hp
    S.toRepresentation (hp.subrepresentation S) (hi i) f hf⟩

end
end Math.CompactMultiplicityIndex
