import Physics.StandardModel.Operators.BnvSevenNegativeTransport

open Math

/-! Negative dimension-seven families in explicit residual coordinates.
The residual modules remain independent of those in the positive families. -/
namespace GUT.BnvSevenNegativeCoordinates
set_option autoImplicit false
noncomputable section
open Representation BnvSevenNegativeTransport
open scoped TensorProduct

variable {R : Type*} [Group R] {F : DeltaLOneSignedInput.Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s)) (p : Fin 4)

abbrev Coordinates := Index p → IntertwiningMap
  (BnvSevenFieldTensor.flavorTensor flavor scalarFlavor (pattern p) (scalar p))
  (Representation.trivial ℂ R ℂ)

def rawEquiv : InvariantCoefficientTransport.Invariants
    (BnvSevenFieldTensor.representation flavor scalarFlavor (pattern p) (scalar p)) ≃ₗ[ℂ]
    Coordinates flavor scalarFlavor p :=
  flavorAlongEquiv (R := R)
    (X := ((F (pattern p 0) ⊗[ℂ] F (pattern p 1)) ⊗[ℂ]
      (F (pattern p 2) ⊗[ℂ] F (pattern p 3))) ⊗[ℂ] S (scalar p))
    (B := FourTensorMultilinear.Tensor
      (fun i => DeltaLOneSignedFields.Field (F := F) (pattern p i)) ⊗[ℂ]
        BnvMixedInput.ScalarField (S := S) (scalar p)) p
    (BnvSevenFieldTensor.flavorTensor flavor scalarFlavor (pattern p) (scalar p))
    (BnvSevenFieldTensor.representation flavor scalarFlavor (pattern p) (scalar p))
    (BnvSevenFieldTensor.regroup flavor scalarFlavor (pattern p) (scalar p))

def orderedSynthesis := (BnvSevenFieldTensor.evaluateMap flavor scalarFlavor
  (pattern p) (scalar p)).comp (rawEquiv flavor scalarFlavor p).symm.toLinearMap

abbrev ordered := MixedSinglePatternAssembly.orderedSpace
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
    (pattern p) (scalar p)

def residualSpace := (ordered flavor scalarFlavor p).comap
  (orderedSynthesis flavor scalarFlavor p)

theorem mem_residualSpace_iff (q : Coordinates flavor scalarFlavor p) :
    q ∈ residualSpace flavor scalarFlavor p ↔ TypedPatternAlternation.Compatible
      (V := DeltaLOneSignedFields.Field (F := F))
      (pattern p) (orderedSynthesis flavor scalarFlavor p q) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨((BnvSevenFieldTensor.tensorDescent flavor scalarFlavor (pattern p) (scalar p)).symm
      ((rawEquiv flavor scalarFlavor p).symm q)).property, h⟩

def tensorEquiv : BnvSevenFieldTensor.tensorSector flavor scalarFlavor (pattern p) (scalar p) ≃ₗ[ℂ]
    residualSpace flavor scalarFlavor p :=
  (rawEquiv flavor scalarFlavor p).ofSubmodules _ _ (by
    simpa only [residualSpace, ordered, orderedSynthesis, BnvSevenFieldTensor.tensorSector,
      Submodule.comap_comp] using
      (BnvSevenFieldTensor.tensorSector flavor scalarFlavor (pattern p) (scalar p)).map_equiv_eq_comap_symm
        (rawEquiv flavor scalarFlavor p))

def orderedEquiv : ordered flavor scalarFlavor p ≃ₗ[ℂ]
    residualSpace flavor scalarFlavor p :=
  (BnvSevenFieldTensor.orderedEquiv flavor scalarFlavor (pattern p) (scalar p)).trans
    (tensorEquiv flavor scalarFlavor p)

theorem forbidden_iff : (∀ f : ordered flavor scalarFlavor p, f = 0) ↔
    ∀ q : residualSpace flavor scalarFlavor p, q = 0 := by
  constructor
  · intro h q
    have hz := h ((orderedEquiv flavor scalarFlavor p).symm q)
    exact (orderedEquiv flavor scalarFlavor p).symm.injective
      (hz.trans (orderedEquiv flavor scalarFlavor p).symm.map_zero.symm)
  · intro h f
    exact (orderedEquiv flavor scalarFlavor p).injective
      ((h ((orderedEquiv flavor scalarFlavor p) f)).trans
        (orderedEquiv flavor scalarFlavor p).map_zero.symm)

end
end GUT.BnvSevenNegativeCoordinates
