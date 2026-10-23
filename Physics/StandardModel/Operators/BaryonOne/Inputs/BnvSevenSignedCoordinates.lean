import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenResidualCoordinates
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenNegativeCoordinates
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenFamilyDecomposition

/-! All eight one-Higgs BNV families, with explicit residual Hom factors. -/
namespace Physics.BnvSevenSignedCoordinates
set_option autoImplicit false
noncomputable section
open Representation

variable {R : Type*} [Group R] {F : DeltaLOneSignedInput.Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

abbrev Factor : Fin 8 → Type _
  | 0 => BnvSevenResidualCoordinates.residualSpace flavor scalarFlavor 0
  | 1 => BnvSevenResidualCoordinates.residualSpace flavor scalarFlavor 1
  | 2 => BnvSevenResidualCoordinates.residualSpace flavor scalarFlavor 2
  | 3 => BnvSevenResidualCoordinates.residualSpace flavor scalarFlavor 3
  | 4 => BnvSevenNegativeCoordinates.residualSpace flavor scalarFlavor 0
  | 5 => BnvSevenNegativeCoordinates.residualSpace flavor scalarFlavor 1
  | 6 => BnvSevenNegativeCoordinates.residualSpace flavor scalarFlavor 2
  | 7 => BnvSevenNegativeCoordinates.residualSpace flavor scalarFlavor 3

instance (i : Fin 8) : AddCommGroup (Factor flavor scalarFlavor i) := match i with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
instance (i : Fin 8) : Module ℂ (Factor flavor scalarFlavor i) := match i with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance

def factorEquiv (i : Fin 8) :
    BnvSevenFamilyDecomposition.OrderedSector flavor scalarFlavor i ≃ₗ[ℂ]
    Factor flavor scalarFlavor i := match i with
  | 0 => BnvSevenResidualCoordinates.orderedEquiv flavor scalarFlavor 0
  | 1 => BnvSevenResidualCoordinates.orderedEquiv flavor scalarFlavor 1
  | 2 => BnvSevenResidualCoordinates.orderedEquiv flavor scalarFlavor 2
  | 3 => BnvSevenResidualCoordinates.orderedEquiv flavor scalarFlavor 3
  | 4 => BnvSevenNegativeCoordinates.orderedEquiv flavor scalarFlavor 0
  | 5 => BnvSevenNegativeCoordinates.orderedEquiv flavor scalarFlavor 1
  | 6 => BnvSevenNegativeCoordinates.orderedEquiv flavor scalarFlavor 2
  | 7 => BnvSevenNegativeCoordinates.orderedEquiv flavor scalarFlavor 3

def equiv : BnvMixedInput.bnvSector flavor scalarFlavor 4 1 ≃ₗ[ℂ]
    (∀ i, Factor flavor scalarFlavor i) :=
  (BnvSevenFamilyDecomposition.orderedEquiv flavor scalarFlavor).trans
    (LinearEquiv.piCongrRight (factorEquiv flavor scalarFlavor))

theorem nonzero_iff : (∃ f : BnvMixedInput.bnvSector flavor scalarFlavor 4 1, f ≠ 0) ↔
    ∃ i, ∃ q : Factor flavor scalarFlavor i, q ≠ 0 :=
  Math.FiniteSpeciesProjection.nonzero_iff_pi
    (A := BnvMixedInput.bnvSector flavor scalarFlavor 4 1) (J := Fin 8)
    (B := fun i => Factor flavor scalarFlavor i) (equiv flavor scalarFlavor)

theorem forbidden_iff : (∀ f : BnvMixedInput.bnvSector flavor scalarFlavor 4 1, f = 0) ↔
    ∀ i, ∀ q : Factor flavor scalarFlavor i, q = 0 := by
  simpa only [not_exists, not_not] using not_congr (nonzero_iff flavor scalarFlavor)

end
end Physics.BnvSevenSignedCoordinates
