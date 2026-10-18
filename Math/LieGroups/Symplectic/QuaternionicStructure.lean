import Math.LieGroups.Symplectic.Torus
import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
import TauCeti.RepresentationTheory.QuaternionicStructure
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! The actual compact symplectic defining action commutes with the
conjugate-linear map v |-> J conjugate(v). Its square is -1 and its
eigenvector pairs are orthogonal. These are inputs for paired spectral
decomposition, not a proof of all-element torus conjugacy. -/

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix

namespace Math.CompactSymplectic

noncomputable section

def defining (n : ℕ) : Representation ℂ (Group n) (Index n → ℂ) :=
  (TauCeti.stdSymplecticRep ℂ n).comp (toSymplectic n)

theorem defining_apply {n : ℕ} (g : Group n) (v : Index n → ℂ) :
    defining n g v = matrix g *ᵥ v :=
  TauCeti.stdSymplecticRep_apply_apply ℂ n (toSymplectic n g) v

theorem defining_pairing {n : ℕ} (g : Group n) (v w : Index n → ℂ) :
    star (defining n g v) ⬝ᵥ defining n g w = star v ⬝ᵥ w := by
  simp only [defining_apply, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hu : (matrix g).conjTranspose * matrix g = 1 := g.val.property.1
  rw [hu, Matrix.one_mulVec]

def quaternionicMap (n : ℕ) : (Index n → ℂ) →ₛₗ[starRingEnd ℂ] (Index n → ℂ) where
  toFun v := Sum.elim (fun i => -star (v (.inr i))) (fun i => star (v (.inl i)))
  map_add' v w := by
    ext i
    cases i <;> simp [add_comm]
  map_smul' c v := by
    ext i
    cases i <;> simp [smul_eq_mul, mul_neg]

theorem quaternionicMap_matrix {n : ℕ} (v : Index n → ℂ) :
    quaternionicMap n v = Matrix.J (Fin n) ℂ *ᵥ star v := by
  ext i
  cases i <;> simp [quaternionicMap, Matrix.J, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec]

theorem quaternionicMap_square {n : ℕ} (v : Index n → ℂ) :
    quaternionicMap n (quaternionicMap n v) = -v := by
  ext i
  cases i <;> simp [quaternionicMap]

theorem matrix_mul_J {n : ℕ} (g : Group n) :
    matrix g * Matrix.J (Fin n) ℂ = Matrix.J (Fin n) ℂ * (matrix g).map star := by
  have hs := (SymplecticGroup.mem_iff.mp (matrix_symplectic g))
  have hu : (matrix g).transpose * (matrix g).map star = 1 := by
    have h : (matrix g).conjTranspose * matrix g = 1 := g.val.property.1
    simpa only [Matrix.transpose_mul, Matrix.conjTranspose_transpose, Matrix.transpose_one]
      using congrArg Matrix.transpose h
  have hh := congrArg (fun A : Mat n => A * (matrix g).map star) hs
  simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using hh

theorem quaternionicMap_intertwines {n : ℕ} (g : Group n) (v : Index n → ℂ) :
    quaternionicMap n (defining n g v) = defining n g (quaternionicMap n v) := by
  simp only [defining_apply, quaternionicMap_matrix]
  have hs : star (matrix g *ᵥ v) = (matrix g).map star *ᵥ star v :=
    funext (RingHom.map_mulVec (starRingEnd ℂ) (matrix g) v)
  rw [hs, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matrix_mul_J]

theorem defining_quaternionic (n : ℕ) :
    (defining n).IsQuaternionicStructure (quaternionicMap n) :=
  ⟨quaternionicMap_square, quaternionicMap_intertwines⟩

theorem quaternionicMap_ne_zero {n : ℕ} {v : Index n → ℂ} (hv : v ≠ 0) :
    quaternionicMap n v ≠ 0 := by
  intro he
  apply hv
  exact (defining_quaternionic n).bijective.injective (he.trans (map_zero _).symm)

theorem quaternionicMap_orthogonal {n : ℕ} (v : Index n → ℂ) :
    star v ⬝ᵥ quaternionicMap n v = 0 := by
  simp only [dotProduct, Fintype.sum_sum_type, quaternionicMap, LinearMap.coe_mk,
    AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, Pi.star_apply, mul_neg, Finset.sum_neg_distrib]
  rw [show (∑ i : Fin n, star (v (.inr i)) * star (v (.inl i))) =
      ∑ i : Fin n, star (v (.inl i)) * star (v (.inr i)) by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _]
  exact neg_add_cancel _

theorem quaternionicMap_eigen {n : ℕ} (g : Group n) {v : Index n → ℂ} {c : ℂ}
    (hv : defining n g v = c • v) :
    defining n g (quaternionicMap n v) = star c • quaternionicMap n v := by
  rw [← quaternionicMap_intertwines, hv, map_smulₛₗ]
  rfl

theorem quaternionicMap_circle_eigen {n : ℕ} (g : Group n) {v : Index n → ℂ} {z : Circle}
    (hv : defining n g v = (z : ℂ) • v) :
    defining n g (quaternionicMap n v) = ((z⁻¹ : Circle) : ℂ) • quaternionicMap n v := by
  rw [Circle.coe_inv_eq_conj]
  exact quaternionicMap_eigen g hv

theorem quaternionicMap_pair_independent {n : ℕ} {v : Index n → ℂ} (hv : v ≠ 0) :
    LinearIndependent ℂ ![v, quaternionicMap n v] := by
  rw [linearIndependent_fin2]
  refine ⟨quaternionicMap_ne_zero hv, ?_⟩
  intro c he
  have hh := congrArg (fun w => star v ⬝ᵥ w) he
  change star v ⬝ᵥ (c • quaternionicMap n v) = star v ⬝ᵥ v at hh
  rw [dotProduct_smul, quaternionicMap_orthogonal, smul_zero] at hh
  exact hv (dotProduct_star_self_eq_zero.mp hh.symm)

theorem quaternionicMap_pairing {n : ℕ} (v w : Index n → ℂ) :
    star (quaternionicMap n v) ⬝ᵥ quaternionicMap n w = star (star v ⬝ᵥ w) := by
  simp [dotProduct, Fintype.sum_sum_type, quaternionicMap, mul_comm, add_comm]

theorem quaternionicMap_preserves_orthogonal_pair {n : ℕ} (v w : Index n → ℂ)
    (hw : star v ⬝ᵥ w = 0) (hjw : star (quaternionicMap n v) ⬝ᵥ w = 0) :
    star v ⬝ᵥ quaternionicMap n w = 0 ∧
      star (quaternionicMap n v) ⬝ᵥ quaternionicMap n w = 0 := by
  constructor
  · have hh := quaternionicMap_pairing (quaternionicMap n v) w
    simpa only [quaternionicMap_square, star_neg, neg_dotProduct, hjw, star_zero,
      neg_eq_zero] using hh
  · rw [quaternionicMap_pairing, hw, star_zero]

end

end Math.CompactSymplectic
