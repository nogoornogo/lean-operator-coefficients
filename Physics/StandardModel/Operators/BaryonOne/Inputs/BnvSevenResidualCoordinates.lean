import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenLocalTransport

open Math

/-! Positive dimension-seven families as explicit residual-Hom coordinates
with the actual typed statistics transported through a two-sided inverse. -/
namespace Physics.BnvSevenResidualCoordinates
set_option autoImplicit false
noncomputable section
open Representation BnvSevenPatternDescent
open scoped TensorProduct

variable {R : Type*} [Group R] {F : DeltaLOneSignedInput.Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s)) (p : Fin 4)

abbrev Coordinates := BnvSevenLocalTransport.Index p → IntertwiningMap
  (BnvSevenFieldTensor.flavorTensor flavor scalarFlavor (pattern p) (scalar p))
  (Representation.trivial ℂ R ℂ)

def rawEquiv : InvariantCoefficientTransport.Invariants
    (BnvSevenFieldTensor.representation flavor scalarFlavor (pattern p) (scalar p)) ≃ₗ[ℂ]
    Coordinates flavor scalarFlavor p :=
  BnvSevenLocalTransport.flavorAlongEquiv (R := R)
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

def residualSpace := (MixedSinglePatternAssembly.orderedSpace
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
    (pattern p) (scalar p)).comap (orderedSynthesis flavor scalarFlavor p)

/-- The residual factors have only the actual typed exchange relations;
local invariance and reconstruction have already been proved, not assumed. -/
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
    simpa only [residualSpace, orderedSynthesis, BnvSevenFieldTensor.tensorSector,
      Submodule.comap_comp] using
      (BnvSevenFieldTensor.tensorSector flavor scalarFlavor (pattern p) (scalar p)).map_equiv_eq_comap_symm
        (rawEquiv flavor scalarFlavor p))

def orderedEquiv : BnvSevenPatternDescent.ordered flavor scalarFlavor p ≃ₗ[ℂ]
    residualSpace flavor scalarFlavor p :=
  (BnvSevenFieldTensor.orderedEquiv flavor scalarFlavor (pattern p) (scalar p)).trans
    (tensorEquiv flavor scalarFlavor p)

def familyEquiv : BnvSevenPatternDescent.family flavor scalarFlavor p ≃ₗ[ℂ]
    residualSpace flavor scalarFlavor p :=
  (BnvSevenPatternDescent.equiv flavor scalarFlavor p).trans
    (orderedEquiv flavor scalarFlavor p)

theorem nonzero_iff : (∃ f : BnvSevenPatternDescent.family flavor scalarFlavor p, f ≠ 0) ↔
    ∃ q : residualSpace flavor scalarFlavor p, q ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨familyEquiv flavor scalarFlavor p f, ?_⟩
    intro hz
    exact hf ((familyEquiv flavor scalarFlavor p).injective
      (hz.trans (familyEquiv flavor scalarFlavor p).map_zero.symm))
  · rintro ⟨q, hq⟩
    refine ⟨(familyEquiv flavor scalarFlavor p).symm q, ?_⟩
    intro hz
    exact hq ((familyEquiv flavor scalarFlavor p).symm.injective
      (hz.trans (familyEquiv flavor scalarFlavor p).symm.map_zero.symm))

theorem forbidden_iff : (∀ f : BnvSevenPatternDescent.family flavor scalarFlavor p, f = 0) ↔
    ∀ q : residualSpace flavor scalarFlavor p, q = 0 := by
  simpa only [not_exists, not_not] using not_congr (nonzero_iff flavor scalarFlavor p)

end
end Physics.BnvSevenResidualCoordinates
