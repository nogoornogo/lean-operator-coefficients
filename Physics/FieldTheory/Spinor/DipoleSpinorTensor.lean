import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.TwoComponentContractions
import Math.RepresentationTheory.InvariantEvaluation
import Math.RepresentationTheory.TwoComponentSymmetricSquare

open Math

/-! One chosen chiral field strength as the dual symmetric two-spinor
module. This is an algebraic spinor convention, not a real two-form theorem. -/
namespace GUT.DipoleSpinorTensor
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor TwoComponentTensorUniqueness
open scoped TensorProduct

abbrev Strength := Module.Dual ℂ Triplet
def strength : Representation ℂ WeylSpinor.Group Strength := triplet.dual
def localRepresentation := (WeylSpinor.left.tprod WeylSpinor.left).tprod strength

def contraction : IntertwiningMap localRepresentation
    (Representation.trivial ℂ WeylSpinor.Group ℂ) :=
  InvariantEvaluation.contraction (WeylSpinor.left.tprod WeylSpinor.left) triplet pair

def coordinate : Module.Dual ℂ Triplet := (Pi.basisFun ℂ (Fin 3)).coord 0
def witness := (basis2 0 ⊗ₜ[ℂ] basis2 0) ⊗ₜ[ℂ] coordinate

@[simp] theorem contraction_tmul (s t : WeylSpinor.Space) (F : Strength) :
    contraction ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] F) = F (pair (s ⊗ₜ[ℂ] t)) := rfl

@[simp] theorem normalized : contraction witness = 1 := by
  simp [witness, coordinate, basis2, Module.Basis.coord_apply]

theorem unique (f : IntertwiningMap localRepresentation
    (Representation.trivial ℂ WeylSpinor.Group ℂ)) : f = f witness • contraction := by
  apply InvariantEvaluation.unique (WeylSpinor.left.tprod WeylSpinor.left) triplet pair
    (basis2 0 ⊗ₜ[ℂ] basis2 0) coordinate
  · exact normalized
  · intro k
    exact ⟨value (MonoidHom.id _) k 0 0 0, TwoComponentContractions.sl_unique k⟩

theorem symmetric (s t : WeylSpinor.Space) (F : Strength) :
    contraction ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] F) =
      contraction ((t ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] F) := by
  simp only [contraction_tmul, pair_symmetric]

end
end GUT.DipoleSpinorTensor
