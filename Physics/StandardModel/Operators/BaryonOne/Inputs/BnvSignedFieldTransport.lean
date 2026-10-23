import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvLocalConjugation
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenNegativeTransport
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneCoefficientCompleteness

open Math

/-! Charge reversal changes the local group action and reindexes independent
flavor inputs. It requires no identification of opposite flavor carriers. -/
namespace Physics.BnvSignedFieldTransport
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor DeltaLOneSignedInput

def opposite : Equiv.Perm Species :=
  Function.Involutive.toPerm BnvLocalConjugation.opposite BnvLocalConjugation.opposite_involutive

@[simp] theorem opposite_twice (s : Species) : opposite (opposite s) = s :=
  BnvLocalConjugation.opposite_involutive s

theorem lepton_opposite (s : Species) : lepton (opposite s) = -lepton s := by
  fin_cases s <;> rfl

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  (flavor : ∀ s, Representation ℂ R (F s))

abbrev Reindexed (s : Species) := F (opposite s)
def reindexed (s : Species) : Representation ℂ R (Reindexed (F := F) s) := flavor (opposite s)

def groupMap := BnvLocalConjugation.conjugate.prodMap (MonoidHom.id R)

theorem groupMap_surjective : Function.Surjective (groupMap (R := R)) := by
  rintro ⟨g,r⟩
  obtain ⟨h,hh⟩ := BnvLocalConjugation.surjective g
  exact ⟨(h,r), by simp [groupMap, hh]⟩

def localRelabel {s t : Species} (h : s = t) : Representation.Equiv
    (DeltaLOneSignedFields.localField s) (DeltaLOneSignedFields.localField t) := by
  subst t
  exact Representation.Equiv.refl _

def localOpposite (s : Species) : Representation.Equiv
    (DeltaLOneSignedFields.localField (opposite s))
    ((DeltaLOneSignedFields.localField s).comp BnvLocalConjugation.conjugate) :=
  (BnvLocalConjugation.localField (opposite s)).trans
    (BnvSevenNegativeTransport.restrictEquiv
      (localRelabel (BnvLocalConjugation.opposite_involutive s)) BnvLocalConjugation.conjugate)

def field (s : Species) : Representation.Equiv
    (DeltaLOneSignedFields.field flavor (opposite s))
    ((DeltaLOneSignedFields.field (reindexed flavor) s).comp (groupMap (R := R))) where
  toLinearEquiv := TensorProduct.congr (localOpposite s).toLinearEquiv
    (LinearEquiv.refl ℂ (F (opposite s)))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun z => z ⊗ₜ[ℂ] flavor (opposite s) g.2 y)
      (LinearMap.congr_fun ((localOpposite s).isIntertwining' g.1) x)

def full : Representation.Equiv (DeltaLOneSignedFields.fullRepresentation flavor)
    ((DeltaLOneSignedFields.fullRepresentation (reindexed flavor)).comp (groupMap (R := R))) where
  toLinearEquiv := (LinearEquiv.piCongrLeft' ℂ
    (DeltaLOneSignedFields.Field (F := F)) opposite).trans
      (LinearEquiv.piCongrRight (fun s => (field flavor s).toLinearEquiv))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext s
    exact LinearMap.congr_fun ((field flavor s).isIntertwining' g) (x (opposite s))

theorem full_apply (x : ∀ s, DeltaLOneSignedFields.Field (F := F) s) (s : Species) :
    full flavor x s = field flavor s (x (opposite s)) := rfl

theorem full_single (s : Species) (x : DeltaLOneSignedFields.Field (F := F) (opposite s)) :
    full flavor (Pi.single (opposite s) x) = Pi.single s (field flavor s x) := by
  funext t
  rw [full_apply]
  by_cases h : t = s
  · subst t
    simp
  · have hn : opposite t ≠ opposite s := fun he => h (opposite.injective he)
    simp [h, hn]

theorem full_supported (s : Species) (x : DeltaLOneSignedFields.Field (F := F) s) :
    full flavor (Pi.single s x) =
      Pi.single (opposite s) (full flavor (Pi.single s x) (opposite s)) := by
  funext t
  by_cases h : t = opposite s
  · subst t; simp
  · have hn : opposite t ≠ s := by
      intro he
      apply h
      have hh := congrArg opposite he
      simpa only [opposite_twice] using hh
    simp [full_apply, h, hn]

theorem full_symm_single (s : Species)
    (y : DeltaLOneSignedFields.Field (F := Reindexed (F := F)) s) :
    (full flavor).symm (Pi.single s y) =
      Pi.single (opposite s) ((field flavor s).symm y) := by
  apply (full flavor).injective
  change full flavor ((full flavor).symm (Pi.single s y)) =
    full flavor (Pi.single (opposite s) ((field flavor s).symm y))
  rw [Representation.Equiv.apply_symm_apply, full_single]
  simp

def exterior : Representation.Equiv
    ((DeltaLOneSignedFields.fullRepresentation flavor).exteriorPower 4)
    (((DeltaLOneSignedFields.fullRepresentation (reindexed flavor)).exteriorPower 4).comp
      (groupMap (R := R))) where
  toLinearEquiv := ((full flavor).exteriorPower 4).toLinearEquiv
  isIntertwining' g := ((full flavor).exteriorPower 4).isIntertwining' g

def coefficientEquiv : DeltaLOneSignedInput.Coefficient (DeltaLOneSignedFields.field flavor) ≃ₗ[ℂ]
    DeltaLOneSignedInput.Coefficient (DeltaLOneSignedFields.field (reindexed flavor)) :=
  (InvariantCoefficientTransport.alongEquiv (exterior flavor)).trans
    (InvariantCoefficientTransport.alongSurjection _ (groupMap (R := R)) groupMap_surjective)

theorem extract_pure (f : DeltaLOneSignedInput.Coefficient (DeltaLOneSignedFields.field flavor))
    (v : Fin 4 → ∀ s, DeltaLOneSignedFields.Field (F := Reindexed (F := F)) s) :
    coefficientEquiv flavor f (exteriorPower.ιMulti ℂ 4 v) =
      f (exteriorPower.ιMulti ℂ 4 (fun i => (full flavor).symm (v i))) := by
  change f (((full flavor).exteriorPower 4).symm (exteriorPower.ιMulti ℂ 4 v)) = _
  apply congrArg f
  apply ((full flavor).exteriorPower 4).injective
  change ((full flavor).exteriorPower 4)
      (((full flavor).exteriorPower 4).symm (exteriorPower.ιMulti ℂ 4 v)) =
    ((full flavor).exteriorPower 4)
      (exteriorPower.ιMulti ℂ 4 (fun i => (full flavor).symm (v i)))
  rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.exteriorPower_apply_ιMulti]
  congr 1
  funext i
  exact ((full flavor).apply_symm_apply (v i)).symm

theorem reconstruct_pure
    (f : DeltaLOneSignedInput.Coefficient (DeltaLOneSignedFields.field (reindexed flavor)))
    (v : Fin 4 → ∀ s, DeltaLOneSignedFields.Field (F := F) s) :
    (coefficientEquiv flavor).symm f (exteriorPower.ιMulti ℂ 4 v) =
      f (exteriorPower.ιMulti ℂ 4 (fun i => full flavor (v i))) := by
  change f (((full flavor).exteriorPower 4) (exteriorPower.ιMulti ℂ 4 v)) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti]
  rfl

theorem opposite_degree (labels : Fin 4 → Species) :
    DeltaLOneSpeciesSupport.leptonDegree (counts (opposite ∘ labels)) =
      -DeltaLOneSpeciesSupport.leptonDegree (counts labels) := by
  rw [lepton_counts, lepton_counts, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact lepton_opposite (labels i)

theorem extract_mem (degree : ℤ)
    (f : DeltaLOneSignedFields.Sector flavor degree) :
    coefficientEquiv flavor f.val ∈ DeltaLOneSignedFields.Sector (reindexed flavor) (-degree) := by
  intro labels hn
  ext v
  rw [FiniteSpeciesExterior.restrict_apply, extract_pure]
  simp only [full_symm_single]
  have hd : DeltaLOneSpeciesSupport.leptonDegree (counts (opposite ∘ labels)) ≠ degree := by
    rw [opposite_degree]
    omega
  have hz := congrArg (fun k => k (fun i => (field flavor (labels i)).symm (v i)))
    (f.property (opposite ∘ labels) hd)
  exact hz

theorem reconstruct_mem (degree : ℤ)
    (f : DeltaLOneSignedFields.Sector (reindexed flavor) (-degree)) :
    (coefficientEquiv flavor).symm f.val ∈ DeltaLOneSignedFields.Sector flavor degree := by
  intro labels hn
  ext v
  rw [FiniteSpeciesExterior.restrict_apply, reconstruct_pure]
  have ht : (fun i => full flavor (Pi.single (labels i) (v i))) =
      (fun i => Pi.single (opposite (labels i))
        (full flavor (Pi.single (labels i) (v i)) (opposite (labels i)))) := by
    funext i
    exact full_supported flavor (labels i) (v i)
  rw [ht]
  have hd : DeltaLOneSpeciesSupport.leptonDegree (counts (opposite ∘ labels)) ≠ -degree := by
    rw [opposite_degree]
    omega
  exact congrArg (fun k => k (fun i =>
    full flavor (Pi.single (labels i) (v i)) (opposite (labels i))))
    (f.property (opposite ∘ labels) hd)

def sectorEquiv (degree : ℤ) : DeltaLOneSignedFields.Sector flavor degree ≃ₗ[ℂ]
    DeltaLOneSignedFields.Sector (reindexed flavor) (-degree) where
  toFun f := ⟨coefficientEquiv flavor f.val, extract_mem flavor degree f⟩
  invFun f := ⟨(coefficientEquiv flavor).symm f.val, reconstruct_mem flavor degree f⟩
  left_inv f := by apply Subtype.ext; exact (coefficientEquiv flavor).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (coefficientEquiv flavor).apply_symm_apply f.val
  map_add' f g := by apply Subtype.ext; exact (coefficientEquiv flavor).map_add f.val g.val
  map_smul' z f := by apply Subtype.ext; exact (coefficientEquiv flavor).map_smul z f.val

def negativeEquiv : DeltaLOneSignedFields.Sector flavor (-1) ≃ₗ[ℂ]
    DeltaLOneCoefficientCompleteness.ResidualProduct (reindexed flavor) :=
  (sectorEquiv flavor (-1)).trans (DeltaLOneCoefficientCompleteness.equiv (reindexed flavor))

end
end Physics.BnvSignedFieldTransport
