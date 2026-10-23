import Physics.FieldTheory.Spinor.Weyl.WeylSpinor
import Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness
import Math.RepresentationTheory.Tensors.TwoComponentContractions

open Math

/-! The independent two-left Weyl invariant space is a normalized invariant line. -/
namespace Physics.WeylPairInvariant
set_option autoImplicit false
noncomputable section
open Representation WeylSpinor SMEpsilonTensor
open scoped TensorProduct

abbrev Coefficient := IntertwiningMap (left.tprod left)
  (Representation.trivial ℂ WeylSpinor.Group ℂ)

def witness : Space ⊗[ℂ] Space := weakBasis 0 ⊗ₜ[ℂ] weakBasis 1

@[simp] theorem epsilon_witness : epsilonLeft witness = 1 := eps2_basis

/-- Restriction to SU(2) already forces the unique alternating contraction. -/
theorem unique (f : Coefficient) : f = f witness • epsilonLeft := by
  have h := SMEpsilonUniqueness.weak_unique (TensorProduct.curry f.toLinearMap)
    (fun g x y => IntertwiningMap.isIntertwining _ _ f
      (TwoComponentContractions.weakToSL g) (x ⊗ₜ[ℂ] y))
  apply IntertwiningMap.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

def coordinateEquiv : Coefficient ≃ₗ[ℂ] ℂ where
  toFun f := f witness
  invFun z := z • epsilonLeft
  left_inv f := (unique f).symm
  right_inv z := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem nonzero_iff (f : Coefficient) : f ≠ 0 ↔ f witness ≠ 0 :=
  not_congr coordinateEquiv.map_eq_zero_iff.symm

theorem apply_formula (f : Coefficient) (x y : Space) :
    f (x ⊗ₜ[ℂ] y) = f witness * eps2 x y := by
  conv_lhs => rw [unique f]
  rfl

end
end Physics.WeylPairInvariant
