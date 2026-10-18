import Physics.StandardModel.Gauge.SMEpsilonTensor
import Math.RepresentationTheory.ExternalInvariantTensor
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Algebraic Weyl spinors for SL(2,C). The right action is entrywise
conjugation, not conjugate transpose. No covering-space classification is used. -/

namespace GUT.WeylSpinor
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor
open scoped TensorProduct

abbrev Group := Matrix.SpecialLinearGroup (Fin 2) ℂ
abbrev Space := Fin 2 → ℂ

def left : Representation ℂ Group Space where
  toFun g := Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

def conjugate : Group →* Group := Matrix.SpecialLinearGroup.map Complex.conjAe.toRingHom
def right : Representation ℂ Group Space := left.comp conjugate

def epsilonLeft : IntertwiningMap (left.tprod left) (Representation.trivial ℂ Group ℂ) where
  toLinearMap := weakTensor
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    exact eps2_invariant _ g.property x y

def epsilonRight : IntertwiningMap (right.tprod right) (Representation.trivial ℂ Group ℂ) where
  toLinearMap := weakTensor
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    exact eps2_invariant _ (conjugate g).property x y

def four : IntertwiningMap ((left.tprod left).tprod (right.tprod right))
    (Representation.trivial ℂ Group ℂ) :=
  (Representation.TensorProduct.lid ℂ (Representation.trivial ℂ Group ℂ)).toIntertwiningMap.comp
    (epsilonLeft.tensor epsilonRight)

@[simp] theorem four_apply (s t u v : Space) :
    four ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v)) = eps2 s t * eps2 u v := rfl

theorem right_apply (g : Group) (x : Space) :
    right g x = ((g : Matrix (Fin 2) (Fin 2) ℂ).map star).mulVec x := rfl

end
end GUT.WeylSpinor
