import Physics.StandardModel.Operators.BnvMixedInput
import Physics.StandardModel.Operators.BnvMixedWeylSupport
import Math.RepresentationTheory.InvariantCoefficientTransport

open Math

/-! The degree-zero boson input is the independent signed exterior input,
including its baryon support condition. Scalar residual actions disappear only
because this degree has no scalar slots. -/
namespace GUT.BnvZeroBosonBridge
set_option autoImplicit false
noncomputable section
open Representation BnvMixedInput DeltaLOneSignedInput

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

def coefficientEquiv : Coefficient flavor scalarFlavor 4 0 ≃ₗ[ℂ]
    FiniteSpeciesExterior.Coefficient (DeltaLOneSignedFields.field flavor) 4 :=
  InvariantCoefficientTransport.alongEquiv
    (MixedWeightSupport.zeroBosonEquiv (DeltaLOneSignedFields.fullRepresentation flavor)
      (scalarRepresentation scalarFlavor) 4)

theorem extraction (f : Coefficient flavor scalarFlavor 4 0)
    (labels : Fin 4 → Species) (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i)) :
    FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field flavor)
      (coefficientEquiv flavor scalarFlavor f) labels v =
    value flavor scalarFlavor f labels (fun i => Fin.elim0 i) v (fun i => Fin.elim0 i) := by
  let e := MixedWeightSupport.zeroBosonEquiv (DeltaLOneSignedFields.fullRepresentation flavor)
    (scalarRepresentation scalarFlavor) 4
  change f (e.symm (exteriorPower.ιMulti ℂ 4 (fun i => Pi.single (labels i) (v i)))) =
    f (MixedWeightSupport.pure (fun i => Pi.single (labels i) (v i))
      (fun i : Fin 0 => Pi.single (Fin.elim0 i) (Fin.elim0 i)))
  apply congrArg f
  apply e.injective
  change e (e.symm _) = e _
  rw [Representation.Equiv.apply_symm_apply]
  exact (MixedWeightSupport.zeroBosonEquiv_pure _ _ 4 _ _).symm

def signedBnv : Submodule ℂ
    (FiniteSpeciesExterior.Coefficient (DeltaLOneSignedFields.field flavor) 4) where
  carrier := {f | ∀ labels v, (∑ i, baryon (labels i)) = 0 →
    FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field flavor) f labels v = 0}
  zero_mem' := by intro labels v hb; rfl
  add_mem' := by
    intro f g hf hg labels v hb
    change FiniteSpeciesExterior.restrict _ f labels v +
      FiniteSpeciesExterior.restrict _ g labels v = 0
    rw [hf labels v hb, hg labels v hb, add_zero]
  smul_mem' := by
    intro z f hf labels v hb
    change z * FiniteSpeciesExterior.restrict _ f labels v = 0
    rw [hf labels v hb, mul_zero]

theorem admissible (f : Coefficient flavor scalarFlavor 4 0) :
    f ∈ bnvSector flavor scalarFlavor 4 0 ↔
      coefficientEquiv flavor scalarFlavor f ∈ signedBnv flavor := by
  constructor
  · intro hf labels v hb
    rw [extraction]
    exact hf labels _ v _ hb
  · intro hf labels scalars v w hb
    have hs : scalars = fun i => Fin.elim0 i := Subsingleton.elim _ _
    subst scalars
    have hw : w = fun i => Fin.elim0 i := Subsingleton.elim _ _
    subst w
    exact (extraction flavor scalarFlavor f labels v).symm.trans (hf labels v hb)

def equiv : bnvSector flavor scalarFlavor 4 0 ≃ₗ[ℂ] signedBnv flavor :=
  (ConstrainedCompleteness.Presentation.mk (coefficientEquiv flavor scalarFlavor)
    (admissible flavor scalarFlavor)).equiv

/-- The lepton grading in the scalar-free BNV degree is a consequence of
invariance; it is not selected in `signedBnv`. -/
theorem lepton_support (f : signedBnv flavor) (labels : Fin 4 → Species)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i))
    (hf : FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field flavor) f.val labels v ≠ 0) :
    DeltaLOneSpeciesSupport.leptonDegree (counts labels) = 1 ∨
      DeltaLOneSpeciesSupport.leptonDegree (counts labels) = -1 := by
  let t : ∀ _ : ScalarSpecies, Representation ℂ R ℂ := fun _ => Representation.trivial ℂ R ℂ
  let q := (equiv flavor t).symm f
  have he : coefficientEquiv flavor t q.val = f.val :=
    congrArg Subtype.val ((equiv flavor t).apply_symm_apply f)
  have hq : value flavor t q.val labels (fun i => Fin.elim0 i)
      v (fun i => Fin.elim0 i) ≠ 0 := by
    rw [← extraction, he]
    exact hf
  have ha := BnvMixedWeylSupport.admissible_of_nonzero flavor t q labels
    (fun i => Fin.elim0 i) v (fun i => Fin.elim0 i) 6 (by norm_num) hq
  exact BnvBoundedSpecies.lepton_at_six _ ha

end
end GUT.BnvZeroBosonBridge
