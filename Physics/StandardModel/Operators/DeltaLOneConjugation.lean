import Physics.StandardModel.Operators.DeltaLOneSignedInput
import Math.RepresentationTheory.ExteriorConjugation

open Math

/-! Typed conjugation of positive and negative lepton-degree sectors. The
model supplies a species-reversing equivariant semilinear field involution;
it is not inferred from a complex-linear duality of multiplicities. -/
namespace GUT.DeltaLOneConjugation
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput

def conjugateSpecies : Equiv.Perm Species :=
  Equiv.swap 0 5 * Equiv.swap 1 6 * Equiv.swap 2 7 * Equiv.swap 3 8 * Equiv.swap 4 9

theorem lepton_conjugate (s : Species) : lepton (conjugateSpecies s) = -lepton s := by
  fin_cases s <;> decide

theorem conjugate_degree (labels : Fin 4 → Species) :
    DeltaLOneSpeciesSupport.leptonDegree (counts (conjugateSpecies ∘ labels)) =
      -DeltaLOneSpeciesSupport.leptonDegree (counts labels) := by
  rw [lepton_counts, lepton_counts, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact lepton_conjugate (labels i)

variable {G : Type*} [Group G] {V : Species → Type*}
  [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  (r : ∀ s, Representation ℂ G (V s))
  (c : (∀ s, V s) ≃ₛₗ[starRingEnd ℂ] (∀ s, V s))
  (hc : ∀ g x, c (FiniteSpeciesExterior.representation r g x) =
    FiniteSpeciesExterior.representation r g (c x))
  (hi : ∀ x, c (c x) = x)
  (hs : ∀ s (x : V s), c (Pi.single s x) =
    Pi.single (conjugateSpecies s) (c (Pi.single s x) (conjugateSpecies s)))

include hs in
theorem conjugate_mem (degree : ℤ) (f : sector r degree) :
    ExteriorConjugation.conjugate (FiniteSpeciesExterior.representation r) c hc f.val ∈
      sector r (-degree) := by
  intro labels hn
  ext v
  rw [FiniteSpeciesExterior.restrict_apply, ExteriorConjugation.conjugate_apply]
  have ht : (fun i => c (Pi.single (labels i) (v i))) =
      (fun i => Pi.single (conjugateSpecies (labels i))
        (c (Pi.single (labels i) (v i)) (conjugateSpecies (labels i)))) := by
    funext i
    exact hs (labels i) (v i)
  rw [ht]
  have hdegree : DeltaLOneSpeciesSupport.leptonDegree
      (counts (conjugateSpecies ∘ labels)) ≠ degree := by
    rw [conjugate_degree]
    omega
  have h := f.property (conjugateSpecies ∘ labels) hdegree
  have he := congrArg (fun k => k
    (fun i => c (Pi.single (labels i) (v i)) (conjugateSpecies (labels i)))) h
  rw [FiniteSpeciesExterior.restrict_apply] at he
  change star (f.val (exteriorPower.ιMulti ℂ 4 (fun i =>
    Pi.single (conjugateSpecies (labels i))
      (c (Pi.single (labels i) (v i)) (conjugateSpecies (labels i)))))) = 0
  simpa only [Function.comp_apply, zero_apply, star_zero] using congrArg star he

/-- Both inverses are checked. In particular nonzero coefficients correspond
without asserting a complex-linear identification of opposite degrees. -/
def equiv (degree : ℤ) : sector r degree ≃ₛₗ[starRingEnd ℂ] sector r (-degree) where
  toFun f := ⟨ExteriorConjugation.conjugate (FiniteSpeciesExterior.representation r) c hc f.val,
    conjugate_mem r c hc hs degree f⟩
  invFun f := ⟨ExteriorConjugation.conjugate (FiniteSpeciesExterior.representation r) c hc f.val,
    by simpa only [neg_neg] using conjugate_mem r c hc hs (-degree) f⟩
  left_inv f := by
    apply Subtype.ext
    exact (ExteriorConjugation.equiv (FiniteSpeciesExterior.representation r) c hc hi).left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact (ExteriorConjugation.equiv (FiniteSpeciesExterior.representation r) c hc hi).right_inv f.val
  map_add' f g := by
    apply Subtype.ext
    exact (ExteriorConjugation.equiv (FiniteSpeciesExterior.representation r) c hc hi).map_add f.val g.val
  map_smul' z f := by
    apply Subtype.ext
    exact (ExteriorConjugation.equiv (FiniteSpeciesExterior.representation r) c hc hi).map_smulₛₗ z f.val

theorem nonzero_iff (degree : ℤ) (f : sector r degree) :
    equiv r c hc hi hs degree f ≠ 0 ↔ f ≠ 0 := by
  exact not_congr (map_eq_zero_iff (equiv r c hc hi hs degree)
    (equiv r c hc hi hs degree).injective)

end
end GUT.DeltaLOneConjugation
