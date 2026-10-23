import Physics.StandardModel.Gauge.Tensors.SMGaugeConjugation
import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenFieldTensor

open Math

/-! Involutive local-group transport. Residual flavor modules are not
conjugated or identified by this construction. -/
namespace Physics.BnvLocalConjugation
set_option autoImplicit false
noncomputable section
open Representation

def opposite : DeltaLOneSignedInput.Species → DeltaLOneSignedInput.Species :=
  ![5,6,7,8,9,0,1,2,3,4]

theorem opposite_involutive : Function.Involutive opposite := by
  intro s
  fin_cases s <;> rfl

def gauge (s : DeltaLOneSignedInput.Species) : Representation.Equiv
    (DeltaLOneSignedFields.gauge s)
    ((DeltaLOneSignedFields.gauge (opposite s)).comp SMGaugeConjugation.conjugate) :=
  match s with
  | 0 => SMGaugeConjugation.unconjugate _ SMGaugeConjugation.quarkDual
  | 1 => SMGaugeConjugation.unconjugate _ SMGaugeConjugation.upDual
  | 2 => SMGaugeConjugation.unconjugate _ SMGaugeConjugation.downDual
  | 3 => SMGaugeConjugation.unconjugate _ SMGaugeConjugation.leptonDual
  | 4 => SMGaugeConjugation.unconjugate _ SMGaugeConjugation.electronDual
  | 5 => SMGaugeConjugation.quarkDual
  | 6 => SMGaugeConjugation.upDual
  | 7 => SMGaugeConjugation.downDual
  | 8 => SMGaugeConjugation.leptonDual
  | 9 => SMGaugeConjugation.electronDual

def oppositeScalar : BnvMixedInput.ScalarSpecies → BnvMixedInput.ScalarSpecies := ![1,0]

def scalar (s : BnvMixedInput.ScalarSpecies) : Representation.Equiv
    (BnvMixedInput.scalarGauge s)
    ((BnvMixedInput.scalarGauge (oppositeScalar s)).comp SMGaugeConjugation.conjugate) :=
  match s with
  | 0 => SMGaugeConjugation.unconjugate _ SMGaugeConjugation.higgsDual
  | 1 => SMGaugeConjugation.higgsDual

theorem spin_involutive : Function.Involutive WeylSpinor.conjugate := by
  intro g
  ext i j
  change star (star ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) = _
  exact star_star _

theorem spin_surjective : Function.Surjective WeylSpinor.conjugate :=
  spin_involutive.surjective

def chirality (b : Bool) : Representation.Equiv
    (FourSameWeylCompleteness.action (!b))
    ((FourSameWeylCompleteness.action b).comp WeylSpinor.conjugate) where
  toLinearEquiv := LinearEquiv.refl ℂ WeylSpinor.Space
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    cases b
    · rfl
    · exact (FourSameWeylCompleteness.right_conjugate g v).symm

def conjugate := SMGaugeConjugation.conjugate.prodMap WeylSpinor.conjugate

theorem involutive : Function.Involutive conjugate := by
  rintro ⟨g,w⟩
  change (SMGaugeConjugation.conjugate (SMGaugeConjugation.conjugate g),
    WeylSpinor.conjugate (WeylSpinor.conjugate w)) = (g,w)
  rw [SMGaugeConjugation.conjugate_involutive, spin_involutive]

theorem surjective : Function.Surjective conjugate := involutive.surjective

def localField (s : DeltaLOneSignedInput.Species) : Representation.Equiv
    (DeltaLOneSignedFields.localField s)
    ((DeltaLOneSignedFields.localField (opposite s)).comp conjugate) where
  toLinearEquiv := TensorProduct.congr (gauge s).toLinearEquiv
    (LinearEquiv.refl ℂ WeylSpinor.Space)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro a b
    change (gauge s) (DeltaLOneSignedFields.gauge s g.1 a) ⊗ₜ[ℂ]
      FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded s) g.2 b =
      DeltaLOneSignedFields.gauge (opposite s) (SMGaugeConjugation.conjugate g.1)
        ((gauge s) a) ⊗ₜ[ℂ]
      FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded (opposite s))
        (WeylSpinor.conjugate g.2) b
    have h := LinearMap.congr_fun ((gauge s).isIntertwining' g.1) a
    change (gauge s) (DeltaLOneSignedFields.gauge s g.1 a) =
      DeltaLOneSignedFields.gauge (opposite s) (SMGaugeConjugation.conjugate g.1)
        ((gauge s) a) at h
    rw [h]
    congr 1
    fin_cases s <;>
      first | rfl | exact (FourSameWeylCompleteness.right_conjugate g.2 b).symm

def localScalar (s : BnvMixedInput.ScalarSpecies) : Representation.Equiv
    (BnvSevenFieldTensor.localScalar s)
    ((BnvSevenFieldTensor.localScalar (oppositeScalar s)).comp conjugate) where
  toLinearEquiv := (scalar s).toLinearEquiv
  isIntertwining' g := (scalar s).isIntertwining' g.1

def tensorPullback {G H A B : Type*} [Group G] [Group H]
    [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    (a : Representation ℂ H A) (b : Representation ℂ H B) (f : G →* H) :
    Representation.Equiv (Representation.tprod (a.comp f) (b.comp f)) ((a.tprod b).comp f) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' _ := rfl

def tensor {A B C D : Type*} [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] [AddCommMonoid C] [Module ℂ C]
    [AddCommMonoid D] [Module ℂ D]
    {a : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) A}
    {b : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) B}
    {c : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) C}
    {d : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) D}
    (e : Representation.Equiv a (c.comp conjugate))
    (f : Representation.Equiv b (d.comp conjugate)) :
    Representation.Equiv (a.tprod b) ((c.tprod d).comp conjugate) :=
  (ExternalInvariantTensor.tensorEquiv e f).trans (tensorPullback c d conjugate)

def five (labels : Fin 4 → DeltaLOneSignedInput.Species)
    (u : BnvMixedInput.ScalarSpecies) : Representation.Equiv
    (BnvSevenFieldTensor.localTensor labels u)
    ((BnvSevenFieldTensor.localTensor (opposite ∘ labels) (oppositeScalar u)).comp conjugate) :=
  tensor (tensor (tensor (localField (labels 0)) (localField (labels 1)))
    (tensor (localField (labels 2)) (localField (labels 3)))) (localScalar u)

end
end Physics.BnvLocalConjugation
