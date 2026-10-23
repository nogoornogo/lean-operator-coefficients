import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedFields
import Math.RepresentationTheory.Content.FiniteSpeciesProjection

open Math

/-! Intrinsic splitting of the full signed-field input into four disjoint
species-count sectors. No contraction basis is used in the splitting. -/
namespace Physics.DeltaLOneFourFamilyDecomposition
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput DeltaLOneSignedFields
open FiniteSpeciesProjection

theorem counts_perm (labels : Fin 4 → Species) (p : Equiv.Perm (Fin 4)) :
    counts (labels ∘ p) = counts labels := by
  have hm (s : Species) : DeltaLOneSignedInput.multiplicity (labels ∘ p) s =
      DeltaLOneSignedInput.multiplicity labels s := by
    unfold DeltaLOneSignedInput.multiplicity
    apply Finset.card_equiv p
    intro i
    simp [Function.comp_apply]
  simp only [counts, hm]

def familyCounts : Fin 4 → DeltaLOneSpeciesSupport.Counts :=
  ![DeltaLOneSpeciesSupport.duql, DeltaLOneSpeciesSupport.qque,
    DeltaLOneSpeciesSupport.qqql, DeltaLOneSpeciesSupport.duue]

def familySupport (i : Fin 4) (labels : Fin 4 → Species) : Prop := counts labels = familyCounts i
instance (i : Fin 4) : DecidablePred (familySupport i) := fun _ => inferInstanceAs (Decidable (_ = _))

theorem stable (i : Fin 4) (labels : Fin 4 → Species) (p : Equiv.Perm (Fin 4)) :
    familySupport i (labels ∘ p) ↔ familySupport i labels := by
  simp only [familySupport, counts_perm]

theorem disjoint (i j : Fin 4) (hij : i ≠ j) (labels : Fin 4 → Species)
    (hi : familySupport i labels) : ¬ familySupport j labels := by
  intro hj
  have he : familyCounts i = familyCounts j := hi.symm.trans hj
  fin_cases i <;> fin_cases j
  all_goals simp_all [familyCounts,
    DeltaLOneSpeciesSupport.duql, DeltaLOneSpeciesSupport.qque,
    DeltaLOneSpeciesSupport.qqql, DeltaLOneSpeciesSupport.duue]

def pattern : Fin 4 → Fin 4 → Species := ![![2,1,0,3], ![0,0,1,4], ![0,0,0,3], ![1,1,2,4]]

theorem counts_pattern (i : Fin 4) : counts (pattern i) = familyCounts i := by
  fin_cases i <;> decide +kernel

theorem multiplicities_eq_of_counts (labels t : Fin 4 → Species) (h : counts labels = counts t)
    (s : Species) : DeltaLOneSignedInput.multiplicity labels s =
      DeltaLOneSignedInput.multiplicity t s := by
  let lookup (n : DeltaLOneSpeciesSupport.Counts) : Species → ℕ :=
    ![n.q,n.u,n.d,n.l,n.e,n.cq,n.cu,n.cd,n.cl,n.ce]
  have hc (xs : Fin 4 → Species) : lookup (counts xs) s =
      DeltaLOneSignedInput.multiplicity xs s := by
    fin_cases s <;> rfl
  rw [← hc labels, ← hc t, h]

theorem orbit (i : Fin 4) (labels : Fin 4 → Species) (h : familySupport i labels) :
    ∃ p : Equiv.Perm (Fin 4), labels ∘ p = pattern i := by
  apply FiniteSpeciesExterior.permutation_of_counts
  intro s
  exact multiplicities_eq_of_counts labels (pattern i) (h.trans (counts_pattern i).symm) s

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

abbrev FamilySector (i : Fin 4) := supportSpace (field flavor) (familySupport i)

/-- No information is lost by extracting a single canonical ordering of a family. -/
theorem family_ext (i : Fin 4) (f g : FamilySector flavor i)
    (h : FiniteSpeciesExterior.restrict (field flavor) f.val (pattern i) =
      FiniteSpeciesExterior.restrict (field flavor) g.val (pattern i)) : f = g :=
  pattern_ext (field flavor) (familySupport i) (pattern i) (orbit i) f g h

theorem sector_eq_partition : DeltaLOneSignedInput.sector (field flavor) 1 =
    partitionSpace (field flavor) familySupport := by
  apply Submodule.ext
  intro f
  constructor
  · intro hf labels hn
    apply vanish_outside_four flavor ⟨f,hf⟩ labels
    intro h
    rcases h with h | h | h | h
    · exact hn ⟨0,h⟩
    · exact hn ⟨1,h⟩
    · exact hn ⟨2,h⟩
    · exact hn ⟨3,h⟩
  · intro hf labels hl
    apply hf labels
    rintro ⟨i,hi⟩
    apply hl
    change counts labels = familyCounts i at hi
    rw [hi]
    fin_cases i <;> rfl

/-- Both inverse identities for the independent full-sector species split. -/
def equiv : Sector flavor 1 ≃ₗ[ℂ] (∀ i : Fin 4, FamilySector flavor i) :=
  (LinearEquiv.ofEq _ _ (sector_eq_partition flavor)).trans
    (partitionEquiv (field flavor) familySupport stable disjoint)

theorem nonzero_iff : (∃ f : Sector flavor 1, f ≠ 0) ↔
    ∃ i : Fin 4, ∃ f : FamilySector flavor i, f ≠ 0 :=
  FiniteSpeciesProjection.nonzero_iff_pi (equiv flavor)

theorem canonical_ext (f g : Sector flavor 1)
    (h : ∀ i : Fin 4,
      FiniteSpeciesExterior.restrict (field flavor) (equiv flavor f i).val (pattern i) =
      FiniteSpeciesExterior.restrict (field flavor) (equiv flavor g i).val (pattern i)) : f = g := by
  apply (equiv flavor).injective
  funext i
  exact family_ext flavor i _ _ (h i)

end
end Physics.DeltaLOneFourFamilyDecomposition
