import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-! Determinant-one coordinates and diagonal matrices. The existing namespace
is retained for compatibility; no UV representation is assumed. -/

set_option autoImplicit false
open scoped BigOperators
namespace Math.SU5.MaximalTorus
noncomputable section

def subgroup : Subgroup (Fin 5 → Circle) where
  carrier := {z | ∏ i, z i = 1}
  one_mem' := by simp
  mul_mem' := by intro z w hz hw; simpa [Finset.prod_mul_distrib] using congrArg₂ (· * ·) hz hw
  inv_mem' := by
    intro z hz
    change (∏ i, (z i)⁻¹) = 1
    rw [Finset.prod_inv_distrib, hz, inv_one]

abbrev Torus := subgroup

@[simp] theorem prod_eq_one (z : Torus) : ∏ i, z.val i = 1 := z.property

def ofCoordinates (z : Fin 4 → Circle) : Torus :=
  ⟨Fin.snoc z (∏ i, z i)⁻¹, by
    change (∏ i : Fin 5, Fin.snoc z (∏ j, z j)⁻¹ i) = 1
    rw [Fin.prod_univ_castSucc]
    change (∏ i, z i) * (∏ i, z i)⁻¹ = 1
    exact mul_inv_cancel _⟩

@[simp] theorem ofCoordinates_castSucc (z : Fin 4 → Circle) (i : Fin 4) :
    (ofCoordinates z).val i.castSucc = z i := by simp [ofCoordinates]

def permute (p : Equiv.Perm (Fin 5)) (z : Torus) : Torus :=
  ⟨z.val ∘ p, (Equiv.prod_comp p z.val).trans z.property⟩

def diagonalElement {n : Type*} [Fintype n] [DecidableEq n]
    (z : n → Circle) (hz : ∏ i, z i = 1) : Matrix.specialUnitaryGroup n ℂ :=
  ⟨Matrix.diagonal (fun i => (z i : ℂ)), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      have hi (i : n) : (z i : ℂ) * star (z i : ℂ) = 1 := by
        rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
        simp
      change Matrix.diagonal (fun i => (z i : ℂ) * star (z i : ℂ)) = 1
      rw [funext hi]
      exact Matrix.diagonal_one
    · rw [Matrix.det_diagonal]
      exact (map_prod Circle.coeHom _ _).symm.trans (congrArg Circle.coeHom hz)⟩

end
end Math.SU5.MaximalTorus
