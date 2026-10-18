import Math.RepresentationTheory.Unitary.SmallSpecialUnitary
import Mathlib.LinearAlgebra.Dual.Basis

/-! Coordinate duality for the defining special unitary representation, with
entrywise conjugation retained as an explicit automorphism of the group. -/
namespace Math.SpecialUnitaryContragredient
set_option autoImplicit false
noncomputable section
open Matrix Representation

def conjugate (n : ℕ) : specialUnitaryGroup (Fin n) ℂ →* specialUnitaryGroup (Fin n) ℂ where
  toFun g := ⟨g.val.map star, by
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · exact map_star_mem_unitaryGroup_iff.mpr g.property.1
    · have h := (starRingEnd ℂ).map_det g.val
      have hg : g.val.det = 1 := g.property.2
      rw [hg, map_one] at h
      exact h.symm⟩
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_mul' g h := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]

theorem conjugate_involutive (n : ℕ) : Function.Involutive (conjugate n) := by
  intro g
  ext i j
  exact star_star _

theorem conjugate_surjective (n : ℕ) : Function.Surjective (conjugate n) :=
  (conjugate_involutive n).surjective

def coordinates (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun

theorem coordinates_apply (n : ℕ) (f : Module.Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    coordinates n f i = f (Pi.single i 1) := by
  simpa only [coordinates, Pi.basisFun_apply] using
    (Pi.basisFun ℂ (Fin n)).dualBasis_equivFun f i

theorem functional_apply (n : ℕ) (f : Module.Dual ℂ (Fin n → ℂ)) (v : Fin n → ℂ) :
    f v = ∑ i, v i * f (Pi.single i 1) := by
  have h := congrArg f ((Pi.basisFun ℂ (Fin n)).sum_repr v)
  simpa only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr,
    smul_eq_mul] using h.symm

def dualEquiv (n : ℕ) : Representation.Equiv (SmallSpecialUnitary.defining n).dual
    ((SmallSpecialUnitary.defining n).comp (conjugate n)) where
  toLinearEquiv := coordinates n
  isIntertwining' g := by
    ext f i
    change coordinates n ((SmallSpecialUnitary.defining n).dual g f) i =
      ((SmallSpecialUnitary.defining n) (conjugate n g) (coordinates n f)) i
    rw [coordinates_apply]
    change f (SmallSpecialUnitary.defining n g⁻¹ (Pi.single i 1)) = _
    rw [functional_apply]
    change (∑ x, ((g⁻¹).val.mulVec (Pi.single i 1)) x * f (Pi.single x 1)) =
      ((g.val.map star).mulVec (coordinates n f)) i
    rw [Matrix.mulVec_single]
    simp only [MulOpposite.op_one, one_smul]
    change (∑ x, star (g.val i x) * f (Pi.single x 1)) =
      ∑ x, star (g.val i x) * coordinates n f x
    simp only [coordinates_apply]

end
end Math.SpecialUnitaryContragredient
