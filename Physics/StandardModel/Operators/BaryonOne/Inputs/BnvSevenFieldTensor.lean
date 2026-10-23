import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenPatternDescent
import Math.RepresentationTheory.Tensors.FourTensorLinearSlot
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

open Math

/-! Actual typed five-field tensors separated into local and residual factors. -/
namespace Physics.BnvSevenFieldTensor
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor DeltaLOneSignedInput

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))
  (labels : Fin 4 → Species) (u : BnvMixedInput.ScalarSpecies)

def localScalar := (BnvMixedInput.scalarGauge u).comp
  (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group)

def localTensor := (FourTensorMultilinear.representation
  (fun i => DeltaLOneSignedFields.localField (labels i))).tprod (localScalar u)

def gaugeTensor := (FourTensorMultilinear.representation
  (fun i => DeltaLOneSignedFields.gauge (labels i))).tprod (BnvMixedInput.scalarGauge u)

def spinTensor := FourTensorMultilinear.representation
  (fun i => FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded (labels i)))

def scalarWithSpin : Representation.Equiv (localScalar u)
    (external (BnvMixedInput.scalarGauge u)
      (Representation.trivial ℂ WeylSpinor.Group ℂ)) :=
  (Representation.TensorProduct.rid ℂ
    ((BnvMixedInput.scalarGauge u).comp
      (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group))).symm

def regroupLocal : Representation.Equiv (localTensor labels u)
    (external (gaugeTensor labels u) (spinTensor labels)) :=
  (tensorEquiv
    (regroupFour (DeltaLOneSignedFields.gauge (labels 0))
      (DeltaLOneSignedFields.gauge (labels 1))
      (DeltaLOneSignedFields.gauge (labels 2))
      (DeltaLOneSignedFields.gauge (labels 3))
      (FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded (labels 0)))
      (FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded (labels 1)))
      (FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded (labels 2)))
      (FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded (labels 3))))
    (scalarWithSpin u)).trans
      ((regroupPair (FourTensorMultilinear.representation
        (fun i => DeltaLOneSignedFields.gauge (labels i))) (BnvMixedInput.scalarGauge u)
        (spinTensor labels) (Representation.trivial ℂ WeylSpinor.Group ℂ)).trans
        (externalEquiv (Representation.Equiv.refl (gaugeTensor labels u))
          (Representation.TensorProduct.rid ℂ (spinTensor labels))))

def flavorTensor := (FourTensorMultilinear.representation
  (fun i => flavor (labels i))).tprod (scalarFlavor u)

def representation := (FourTensorMultilinear.representation
  (fun i => DeltaLOneSignedFields.field flavor (labels i))).tprod
    (BnvMixedInput.scalarField scalarFlavor u)

def tensorDescent := FourTensorLinearSlot.equiv
  (fun i => DeltaLOneSignedFields.field flavor (labels i))
  (BnvMixedInput.scalarField scalarFlavor u)

def evaluateMap : InvariantCoefficientTransport.Invariants
    (representation flavor scalarFlavor labels u) →ₗ[ℂ]
    MultilinearMap ℂ (fun i => DeltaLOneSignedFields.Field (F := F) (labels i))
      (BnvMixedInput.ScalarField (S := S) u →ₗ[ℂ] ℂ) :=
  (FourTensorLinearSlot.maps
    (fun i => DeltaLOneSignedFields.field flavor (labels i))
    (BnvMixedInput.scalarField scalarFlavor u)).subtype.comp
      (tensorDescent flavor scalarFlavor labels u).symm.toLinearMap

/-- Actual identical-field statistics retained after tensor descent. -/
def tensorSector := (MixedSinglePatternAssembly.orderedSpace
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor) labels u).comap
    (evaluateMap flavor scalarFlavor labels u)

def orderedEquiv : MixedSinglePatternAssembly.orderedSpace
    (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor) labels u ≃ₗ[ℂ]
    tensorSector flavor scalarFlavor labels u where
  toFun k := ⟨tensorDescent flavor scalarFlavor labels u ⟨k.val, k.property.1⟩, by
    change evaluateMap flavor scalarFlavor labels u
      (tensorDescent flavor scalarFlavor labels u ⟨k.val, k.property.1⟩) ∈
        MixedSinglePatternAssembly.orderedSpace (DeltaLOneSignedFields.field flavor)
          (BnvMixedInput.scalarField scalarFlavor) labels u
    have h := congrArg Subtype.val ((tensorDescent flavor scalarFlavor labels u).symm_apply_apply
      ⟨k.val, k.property.1⟩)
    change evaluateMap flavor scalarFlavor labels u
      (tensorDescent flavor scalarFlavor labels u ⟨k.val, k.property.1⟩) = k.val at h
    rw [h]
    exact k.property⟩
  invFun f := ⟨evaluateMap flavor scalarFlavor labels u f.val, f.property⟩
  left_inv k := by
    apply Subtype.ext
    change evaluateMap flavor scalarFlavor labels u
      (tensorDescent flavor scalarFlavor labels u ⟨k.val, k.property.1⟩) = k.val
    exact congrArg Subtype.val ((tensorDescent flavor scalarFlavor labels u).symm_apply_apply
      ⟨k.val, k.property.1⟩)
  right_inv f := by
    apply Subtype.ext
    change tensorDescent flavor scalarFlavor labels u
      ((tensorDescent flavor scalarFlavor labels u).symm f.val) = f.val
    exact (tensorDescent flavor scalarFlavor labels u).apply_symm_apply f.val
  map_add' k h := by
    apply Subtype.ext
    exact (tensorDescent flavor scalarFlavor labels u).map_add
      ⟨k.val, k.property.1⟩ ⟨h.val, h.property.1⟩
  map_smul' z k := by
    apply Subtype.ext
    exact (tensorDescent flavor scalarFlavor labels u).map_smul z ⟨k.val, k.property.1⟩

def regroup : Representation.Equiv (representation flavor scalarFlavor labels u)
    (external (localTensor labels u) (flavorTensor flavor scalarFlavor labels u)) :=
  (tensorEquiv
    (regroupFour (DeltaLOneSignedFields.localField (labels 0))
      (DeltaLOneSignedFields.localField (labels 1))
      (DeltaLOneSignedFields.localField (labels 2))
      (DeltaLOneSignedFields.localField (labels 3))
      (flavor (labels 0)) (flavor (labels 1)) (flavor (labels 2)) (flavor (labels 3)))
    (Representation.Equiv.refl (BnvMixedInput.scalarField scalarFlavor u))).trans
      (regroupPair (FourTensorMultilinear.representation
        (fun i => DeltaLOneSignedFields.localField (labels i))) (localScalar u)
        (FourTensorMultilinear.representation (fun i => flavor (labels i))) (scalarFlavor u))

def invariantEquiv :
    InvariantCoefficientTransport.Invariants (representation flavor scalarFlavor labels u) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (external (localTensor labels u) (flavorTensor flavor scalarFlavor labels u)) :=
  InvariantCoefficientTransport.alongEquiv (regroup flavor scalarFlavor labels u)

end
end Physics.BnvSevenFieldTensor
