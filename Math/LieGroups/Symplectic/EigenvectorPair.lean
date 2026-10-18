import Math.LieGroups.Symplectic.QuaternionicStructure
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Every positive-rank compact symplectic matrix has a nonzero orthogonal
pair of eigenvectors with inverse circle eigenvalues. The 1 and -1 cases are
included: independence comes from the quaternionic structure, not from
distinctness of the eigenvalues. A full paired eigenbasis is still separate. -/

set_option autoImplicit false
open scoped ComplexOrder
open Matrix

namespace Math.CompactSymplectic

noncomputable section

theorem defining_eigen_norm {n : ℕ} (g : Group n) {v : Index n → ℂ} {c : ℂ}
    (hv : v ≠ 0) (he : defining n g v = c • v) : ‖c‖ = 1 := by
  have hd : star v ⬝ᵥ v ≠ 0 := mt dotProduct_star_self_eq_zero.mp hv
  have hh := defining_pairing g v v
  rw [he] at hh
  have hc : star c * c = 1 := by
    apply mul_right_cancel₀ hd
    simpa only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_assoc, mul_left_comm,
      one_mul] using hh
  exact CStarRing.norm_of_mem_unitary (show c ∈ unitary ℂ from
    ⟨hc, by simpa only [mul_comm] using hc⟩)

theorem exists_eigenvector_pair {n : ℕ} [NeZero n] (g : Group n) :
    ∃ (z : Circle) (v : Index n → ℂ), v ≠ 0 ∧
      defining n g v = (z : ℂ) • v ∧
      defining n g (quaternionicMap n v) = ((z⁻¹ : Circle) : ℂ) • quaternionicMap n v ∧
      star v ⬝ᵥ quaternionicMap n v = 0 ∧
      LinearIndependent ℂ ![v, quaternionicMap n v] := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (defining n g)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let z : Circle := ⟨c, mem_sphere_zero_iff_norm.mpr (defining_eigen_norm g hv.2 hv.apply_eq_smul)⟩
  refine ⟨z, v, hv.2, hv.apply_eq_smul, ?_, quaternionicMap_orthogonal v,
    quaternionicMap_pair_independent hv.2⟩
  exact quaternionicMap_circle_eigen g hv.apply_eq_smul

theorem defining_preserves_eigen_orthogonal {n : ℕ} (g : Group n)
    {v w : Index n → ℂ} {z : Circle} (he : defining n g v = (z : ℂ) • v)
    (hw : star v ⬝ᵥ w = 0) : star v ⬝ᵥ defining n g w = 0 := by
  have hh := defining_pairing g v w
  rw [he, star_smul, smul_dotProduct, smul_eq_mul, hw] at hh
  exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr (Circle.coe_ne_zero z))

theorem defining_preserves_orthogonal_pair {n : ℕ} (g : Group n)
    {v w : Index n → ℂ} {z : Circle} (he : defining n g v = (z : ℂ) • v)
    (hw : star v ⬝ᵥ w = 0) (hjw : star (quaternionicMap n v) ⬝ᵥ w = 0) :
    star v ⬝ᵥ defining n g w = 0 ∧
      star (quaternionicMap n v) ⬝ᵥ defining n g w = 0 :=
  ⟨defining_preserves_eigen_orthogonal g he hw,
    defining_preserves_eigen_orthogonal g (quaternionicMap_circle_eigen g he) hjw⟩

end

end Math.CompactSymplectic
