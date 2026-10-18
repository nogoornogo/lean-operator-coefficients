import Physics.StandardModel.Operators.BnvSignedFieldTransport
import Physics.StandardModel.Operators.BnvZeroBosonBridge

open Math

/-! The scalar-free signed BNV input, with independent positive and negative
flavor modules, has two complete dimension-six residual products. -/
namespace GUT.BnvSixResidualCompleteness
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput DeltaLOneSignedFields FiniteSpeciesProjection

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

def degree : Fin 2 → ℤ := ![1,-1]
def support (i : Fin 2) (labels : Fin 4 → Species) : Prop :=
  DeltaLOneSpeciesSupport.leptonDegree (counts labels) = degree i
instance (i : Fin 2) : DecidablePred (support i) := fun _ => inferInstanceAs (Decidable (_ = _))

theorem stable (i : Fin 2) (labels : Fin 4 → Species) (p : Equiv.Perm (Fin 4)) :
    support i (labels ∘ p) ↔ support i labels := by
  simp only [support, DeltaLOneFourFamilyDecomposition.counts_perm]

theorem disjoint (i j : Fin 2) (h : i ≠ j) (labels : Fin 4 → Species)
    (hi : support i labels) : ¬ support j labels := by
  fin_cases i <;> fin_cases j <;> simp_all [support, degree]

theorem support_eq_sector (i : Fin 2) :
    supportSpace (field flavor) (support i) = Sector flavor (degree i) := rfl

theorem positive_bnv (f : Sector flavor 1) : f.val ∈ BnvZeroBosonBridge.signedBnv flavor := by
  intro labels v hb
  by_contra hn
  have h := baryonDegree_of_nonzero flavor f labels v hn
  rw [baryon_counts, hb] at h
  norm_num at h

theorem baryon_opposite (s : Species) :
    baryon (BnvSignedFieldTransport.opposite s) = -baryon s := by
  fin_cases s <;> rfl

theorem negative_bnv (f : Sector flavor (-1)) : f.val ∈ BnvZeroBosonBridge.signedBnv flavor := by
  intro labels v hb
  let q : Sector (BnvSignedFieldTransport.reindexed flavor) 1 :=
    BnvSignedFieldTransport.sectorEquiv flavor (-1) f
  let w := fun i => BnvSignedFieldTransport.full flavor (Pi.single (labels i) (v i))
    (BnvSignedFieldTransport.opposite (labels i))
  have hb' : ∑ i, baryon (BnvSignedFieldTransport.opposite (labels i)) = 0 := by
    simp only [baryon_opposite, Finset.sum_neg_distrib, hb, neg_zero]
  have hz := positive_bnv (BnvSignedFieldTransport.reindexed flavor) q
    (BnvSignedFieldTransport.opposite ∘ labels) w hb'
  change f.val (exteriorPower.ιMulti ℂ 4 (fun i => Pi.single (labels i) (v i))) = 0
  have he := BnvSignedFieldTransport.reconstruct_pure flavor q.val
    (fun i => Pi.single (labels i) (v i))
  have hq : (BnvSignedFieldTransport.coefficientEquiv flavor).symm q.val = f.val :=
    (BnvSignedFieldTransport.coefficientEquiv flavor).symm_apply_apply f.val
  rw [hq] at he
  have ht : (fun i => BnvSignedFieldTransport.full flavor (Pi.single (labels i) (v i))) =
    (fun i => Pi.single (BnvSignedFieldTransport.opposite (labels i)) (w i)) := by
    funext i
    exact BnvSignedFieldTransport.full_supported flavor (labels i) (v i)
  rw [ht] at he
  exact he.trans hz

theorem sector_bnv (i : Fin 2) (f : Sector flavor (degree i)) :
    f.val ∈ BnvZeroBosonBridge.signedBnv flavor := by
  fin_cases i
  · exact positive_bnv flavor f
  · exact negative_bnv flavor f

theorem signed_eq_partition : BnvZeroBosonBridge.signedBnv flavor =
    partitionSpace (field flavor) support := by
  apply Submodule.ext
  intro f
  constructor
  · intro hf labels hn
    ext v
    by_contra hv
    rcases BnvZeroBosonBridge.lepton_support flavor ⟨f,hf⟩ labels v hv with h | h
    · exact hn ⟨0,h⟩
    · exact hn ⟨1,h⟩
  · intro hf
    let q := partitionEquiv (field flavor) support stable disjoint ⟨f,hf⟩
    have hq : (join (field flavor) support q).val = f :=
      congrArg Subtype.val (join_split (field flavor) support stable disjoint ⟨f,hf⟩)
    rw [← hq]
    change (∑ i, (q i).val) ∈ BnvZeroBosonBridge.signedBnv flavor
    apply (BnvZeroBosonBridge.signedBnv flavor).sum_mem
    intro i hi
    exact sector_bnv flavor i ⟨(q i).val, (q i).property⟩

abbrev ResidualProduct := DeltaLOneCoefficientCompleteness.ResidualProduct flavor ×
  DeltaLOneCoefficientCompleteness.ResidualProduct (BnvSignedFieldTransport.reindexed flavor)

def sectorProduct : (∀ i : Fin 2, supportSpace (field flavor) (support i)) ≃ₗ[ℂ]
    Sector flavor 1 × Sector flavor (-1) where
  toFun f := (f 0, f 1)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def equiv : BnvZeroBosonBridge.signedBnv flavor ≃ₗ[ℂ] ResidualProduct flavor :=
  (LinearEquiv.ofEq _ _ (signed_eq_partition flavor)).trans
    ((partitionEquiv (field flavor) support stable disjoint).trans
      ((sectorProduct flavor).trans
        (LinearEquiv.prodCongr (DeltaLOneCoefficientCompleteness.equiv flavor)
          (BnvSignedFieldTransport.negativeEquiv flavor))))

theorem forbidden_iff : (∀ f : BnvZeroBosonBridge.signedBnv flavor, f = 0) ↔
    ∀ q : ResidualProduct flavor, q = 0 := by
  constructor
  · intro h q
    exact (equiv flavor).symm.injective
      ((h ((equiv flavor).symm q)).trans (equiv flavor).symm.map_zero.symm)
  · intro h f
    exact (equiv flavor).injective
      ((h ((equiv flavor) f)).trans (equiv flavor).map_zero.symm)

end
end GUT.BnvSixResidualCompleteness
