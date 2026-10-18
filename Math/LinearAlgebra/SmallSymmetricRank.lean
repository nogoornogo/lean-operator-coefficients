import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Exact ranks of the two small symmetric blocks in a two-flavor mass. -/
set_option autoImplicit false
namespace SmallSymmetricRank
noncomputable section
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

def star (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, a, b; a, 0, 0; b, 0, 0]

def singlet (u v w : K) : Matrix (Fin 2) (Fin 2) K := !![u, v; v, w]

theorem star_rank_le (a b : K) : (star a b).rank ≤ 2 := by
  let L : Matrix (Fin 3) (Fin 2) K := !![1, 0; 0, a; 0, b]
  let R : Matrix (Fin 2) (Fin 3) K := !![0, a, b; 1, 0, 0]
  have h : star a b = L * R := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [star, L, R, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [h]
  exact (Matrix.rank_mul_le_left L R).trans L.rank_le_width

theorem star_rank (a b : K) : (star a b).rank = if a = 0 ∧ b = 0 then 0 else 2 := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst a; subst b
      have he : star (0 : K) 0 = 0 := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [he, Matrix.rank_zero]
      simp
    · rw [ite_eq_right (by tauto)]
      apply le_antisymm (star_rank_le a b)
      let f : Fin 2 → Fin 3 := ![0, 2]
      have hd : ((star a b).submatrix f f).det ≠ 0 := by
        rw [Matrix.det_fin_two]
        change 0 * 0 - b * b ≠ 0
        simpa using neg_ne_zero.mpr (mul_ne_zero hb hb)
      have hr := Matrix.rank_of_det_ne_zero hd
      have hl := Matrix.rank_submatrix_le (star a b) f f
      simpa [hr] using hl
  · rw [ite_eq_right (by tauto)]
    apply le_antisymm (star_rank_le a b)
    let f : Fin 2 → Fin 3 := ![0, 1]
    have hd : ((star a b).submatrix f f).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      change 0 * 0 - a * a ≠ 0
      simpa using neg_ne_zero.mpr (mul_ne_zero ha ha)
    have hr := Matrix.rank_of_det_ne_zero hd
    have hl := Matrix.rank_submatrix_le (star a b) f f
    simpa [hr] using hl

theorem diagonal_entry_rank_pos {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (i : n) (hi : A i i ≠ 0) : 1 ≤ A.rank := by
  let f : Fin 1 → n := fun _ => i
  have hd : (A.submatrix f f).det ≠ 0 := by simpa [Matrix.det_fin_one, f] using hi
  have hr := Matrix.rank_of_det_ne_zero hd
  have hl := Matrix.rank_submatrix_le A f f
  simpa [hr] using hl

theorem singlet_rank (u v w : K) : (singlet u v w).rank =
    if u = 0 ∧ v = 0 ∧ w = 0 then 0 else if u * w - v * v = 0 then 1 else 2 := by
  by_cases hz : u = 0 ∧ v = 0 ∧ w = 0
  · rcases hz with ⟨rfl, rfl, rfl⟩
    have he : singlet (0 : K) 0 0 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [he, Matrix.rank_zero]
    simp
  rw [ite_eq_right hz]
  by_cases hd : u * w - v * v = 0
  · rw [ite_eq_left hd]
    by_cases hu : u = 0
    · subst u
      have hv : v = 0 := by simpa using hd
      subst v
      have hw : w ≠ 0 := by tauto
      have he : singlet (0 : K) 0 w = Matrix.vecMulVec ![0, w] ![0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [singlet, Matrix.vecMulVec]
      apply le_antisymm
      · rw [he]; exact Matrix.rank_vecMulVec_le _ _
      · exact diagonal_entry_rank_pos _ 1 hw
    · have he : singlet u v w = Matrix.vecMulVec ![u, v] ![1, v / u] := by
        have hw : w = v * v / u := by apply (eq_div_iff hu).mpr; linear_combination hd
        ext i j
        fin_cases i <;> fin_cases j <;> simp [singlet, Matrix.vecMulVec, hw]
        all_goals field_simp [hu]
      apply le_antisymm
      · rw [he]; exact Matrix.rank_vecMulVec_le _ _
      · exact diagonal_entry_rank_pos _ 0 hu
  · rw [ite_eq_right hd]
    have hdet : (singlet u v w).det ≠ 0 := by simpa [singlet, Matrix.det_fin_two] using hd
    simpa using Matrix.rank_of_det_ne_zero hdet

abbrev Coordinates (K : Type*) := (Fin 10 → K) × ((Fin 5 → Fin 3 → K) × (Fin 2 → K))

def blockMap (a b u v w : K) : Coordinates K →ₗ[K] Coordinates K :=
  (0 : (Fin 10 → K) →ₗ[K] (Fin 10 → K)).prodMap
    ((LinearMap.pi fun i : Fin 5 => (star a b).mulVecLin.comp (LinearMap.proj i)).prodMap
      (singlet u v w).mulVecLin)

theorem mem_block_kernel (a b u v w : K) (x : Coordinates K) :
    x ∈ (blockMap a b u v w).ker ↔
      (∀ i, (star a b).mulVecLin (x.2.1 i) = 0) ∧ (singlet u v w).mulVecLin x.2.2 = 0 := by
  simp [LinearMap.mem_ker, blockMap, funext_iff]

def blockKernelEquiv (a b u v w : K) : (blockMap a b u v w).ker ≃ₗ[K]
    (Fin 10 → K) × ((Fin 5 → (star a b).mulVecLin.ker) × (singlet u v w).mulVecLin.ker) where
  toFun x := (x.val.1,
    ((fun i => ⟨x.val.2.1 i, (mem_block_kernel a b u v w x.val).mp x.property |>.1 i⟩),
      ⟨x.val.2.2, (mem_block_kernel a b u v w x.val).mp x.property |>.2⟩))
  invFun y := ⟨(y.1, ((fun i => (y.2.1 i).val), y.2.2.val)),
    (mem_block_kernel a b u v w _).mpr ⟨fun i => (y.2.1 i).property, y.2.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem matrix_nullity {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank K A.mulVecLin.ker = n - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank K A.mulVecLin.ker = _ at h
  simp only [Module.finrank_fin_fun] at h
  omega

theorem block_nullity (a b u v w : K) :
    Module.finrank K (blockMap a b u v w).ker =
      10 + 5 * (3 - (if a = 0 ∧ b = 0 then 0 else 2)) +
        (2 - (if u = 0 ∧ v = 0 ∧ w = 0 then 0 else if u * w - v * v = 0 then 1 else 2)) := by
  rw [(blockKernelEquiv a b u v w).finrank_eq]
  simp [Module.finrank_prod, Module.finrank_pi_fintype, matrix_nullity, star_rank, singlet_rank,
    Nat.mul_comm, Nat.add_assoc]

theorem block_nullity_cases (a b u v w : K) :
    Module.finrank K (blockMap a b u v w).ker ∈ ({15, 16, 17, 25, 26, 27} : Finset ℕ) := by
  rw [block_nullity]
  split_ifs <;> norm_num

theorem nonzero_coefficients_rank_drop :
    Module.finrank K (blockMap (1 : K) 1 1 1 1).ker = 16 := by
  simp [block_nullity]

end
end SmallSymmetricRank
