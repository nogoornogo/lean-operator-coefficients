import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Unitary congruence of a specified complex diagonal bilinear form.
This uses transpose, not adjoint, in the preservation equation. -/
namespace Math.UnitaryDiagonalCongruence
set_option autoImplicit false
noncomputable section
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def Preserves (c : I → ℂ) (U : Matrix I I ℂ) : Prop :=
  U.transpose * diagonal c * U = diagonal c

theorem bilinear_iff (c : I → ℂ) (U : Matrix I I ℂ) :
    Preserves c U ↔ ∀ x y : I → ℂ,
      (diagonal c).toBilin' (U.toLin' x) (U.toLin' y) = (diagonal c).toBilin' x y := by
  have he : Preserves c U ↔
      (diagonal c).toBilin'.comp U.toLin' U.toLin' = (diagonal c).toBilin' := by
    rw [Matrix.toBilin'_comp]
    exact Matrix.toBilin'.injective.eq_iff.symm
  rw [he]
  constructor
  · intro h x y
    exact congrArg (fun B : LinearMap.BilinForm ℂ (I → ℂ) => B x y) h
  · intro h
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    exact h x y

theorem preserves_iff (c : I → ℂ) (U : Matrix.unitaryGroup I ℂ) :
    Preserves c U.val ↔ diagonal c * U.val = U.val.map star * diagonal c := by
  have hl : U.val.map star * U.val.transpose = 1 := by
    have h := congrArg Matrix.transpose U.property.2
    simpa only [transpose_mul, star_eq_conjTranspose, conjTranspose_transpose,
      transpose_transpose, transpose_one] using h
  have hr : U.val.transpose * U.val.map star = 1 := by
    have h := congrArg Matrix.transpose U.property.1
    simpa only [transpose_mul, star_eq_conjTranspose, conjTranspose_transpose,
      transpose_transpose, transpose_one] using h
  unfold Preserves
  constructor
  · intro h
    have he := congrArg (fun A => U.val.map star * A) h
    simpa only [← Matrix.mul_assoc, hl, one_mul] using he
  · intro h
    calc
      U.val.transpose * diagonal c * U.val = U.val.transpose * (diagonal c * U.val) :=
        Matrix.mul_assoc _ _ _
      _ = U.val.transpose * (U.val.map star * diagonal c) := by rw [h]
      _ = diagonal c := by rw [← Matrix.mul_assoc, hr, one_mul]

theorem entry_iff (c : I → ℂ) (U : Matrix.unitaryGroup I ℂ) :
    Preserves c U.val ↔ ∀ i j, c i * U i j = star (U i j) * c j := by
  rw [preserves_iff]
  constructor
  · intro h i j
    simpa only [diagonal_mul, mul_diagonal, Matrix.map_apply] using
      congrArg (fun A => A i j) h
  · intro h
    ext i j
    simpa only [diagonal_mul, mul_diagonal, Matrix.map_apply] using h i j

/-- The full unitary stabilizer, with no diagonal restriction on its elements. -/
def subgroup (c : I → ℂ) : Subgroup (Matrix.unitaryGroup I ℂ) where
  carrier := fun U => Preserves c U.val
  one_mem' := by change Preserves c (1 : Matrix I I ℂ); simp [Preserves]
  mul_mem' := by
    intro U V hU hV
    change (U.val * V.val).transpose * diagonal c * (U.val * V.val) = diagonal c
    rw [transpose_mul]
    calc
      _ = V.val.transpose * (U.val.transpose * diagonal c * U.val) * V.val := by
        simp only [Matrix.mul_assoc]
      _ = diagonal c := by rw [hU]; exact hV
  inv_mem' := by
    intro U hU
    change Preserves c U.val at hU
    change Preserves c (U⁻¹).val
    rw [entry_iff] at hU ⊢
    intro i j
    simpa only [Matrix.UnitaryGroup.inv_apply, Matrix.star_apply, star_star,
      mul_comm] using (hU j i).symm

theorem no_mixing (c : I → ℂ) (U : Matrix.unitaryGroup I ℂ)
    (h : Preserves c U.val) (i j : I)
    (hij : Complex.normSq (c i) ≠ Complex.normSq (c j)) : U i j = 0 := by
  have he := congrArg Complex.normSq ((entry_iff c U).mp h i j)
  simp only [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj] at he
  have hz : (Complex.normSq (c i) - Complex.normSq (c j)) * Complex.normSq (U i j) = 0 := by
    linear_combination he
  exact Complex.normSq_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij))

/-- In real nonnegative coordinates, different masses cannot mix and every
nonzero-mass block is real. The zero block is unrestricted within U(n). -/
theorem nonnegative_iff (m : I → ℝ) (hm : ∀ i, 0 ≤ m i)
    (U : Matrix.unitaryGroup I ℂ) :
    Preserves (fun i => (m i : ℂ)) U.val ↔
      (∀ i j, m i ≠ m j → U i j = 0) ∧
      (∀ i j, m i ≠ 0 → star (U i j) = U i j) := by
  constructor
  · intro h
    have hcross : ∀ i j, m i ≠ m j → U i j = 0 := by
      intro i j hij
      apply no_mixing _ U h i j
      simp only [Complex.normSq_ofReal]
      intro he
      apply hij
      have he' : (m i - m j) * (m i + m j) = 0 := by nlinarith [he]
      rcases mul_eq_zero.mp he' with hzero | hzero
      · exact sub_eq_zero.mp hzero
      · linarith [hm i, hm j]
    refine ⟨hcross, ?_⟩
    intro i j hi
    by_cases hij : m i = m j
    · have he := (entry_iff _ U).mp h i j
      rw [← hij, mul_comm (star (U i j))] at he
      exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hi) he).symm
    · rw [hcross i j hij, star_zero]
  · rintro ⟨hcross, hreal⟩
    rw [entry_iff]
    intro i j
    by_cases hij : m i = m j
    · rw [← hij]
      by_cases hi : m i = 0
      · simp [hi]
      · rw [hreal i j hi, mul_comm]
    · rw [hcross i j hij, star_zero, mul_zero, zero_mul]

theorem zero_subgroup : subgroup (fun _ : I => 0) = ⊤ := by
  ext U
  change Preserves (fun _ => 0) U.val ↔ True
  simp [Preserves]

theorem constant_iff (r : ℂ) (hr : r ≠ 0) (U : Matrix.unitaryGroup I ℂ) :
    Preserves (fun _ => r) U.val ↔ ∀ i j, star (U i j) = U i j := by
  rw [entry_iff]
  constructor
  · intro h i j
    exact (mul_left_cancel₀ hr (by simpa only [mul_comm r] using h i j)).symm
  · intro h i j
    rw [h i j, mul_comm]

def orthogonalHom (r : ℂ) (hr : r ≠ 0) :
    Matrix.orthogonalGroup I ℝ →* subgroup (fun _ : I => r) where
  toFun A :=
    ⟨⟨A.val.map Complex.ofRealHom, by
        rw [Matrix.mem_unitaryGroup_iff]
        have hs : star (A.val.map Complex.ofRealHom) =
            A.val.transpose.map Complex.ofRealHom := by ext i j; simp [Matrix.star_apply]
        rw [hs]
        change Complex.ofRealHom.mapMatrix A.val * Complex.ofRealHom.mapMatrix A.val.transpose = 1
        have hA := A.property.2
        change A.val * A.val.transpose = 1 at hA
        rw [← map_mul, hA, map_one]⟩,
      (constant_iff r hr _).mpr (by intro i j; simp)⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one Complex.ofRealHom.mapMatrix
  map_mul' A B := by apply Subtype.ext; apply Subtype.ext; exact map_mul Complex.ofRealHom.mapMatrix _ _

theorem orthogonalHom_bijective (r : ℂ) (hr : r ≠ 0) :
    Function.Bijective (orthogonalHom (I := I) r hr) := by
  constructor
  · intro A B h
    apply Subtype.ext
    apply Matrix.map_injective Complex.ofReal_injective
    exact congrArg (fun U : subgroup (fun _ : I => r) => U.val.val) h
  · intro U
    have hreal := (constant_iff r hr U.val).mp U.property
    let A : Matrix I I ℝ := U.val.val.map Complex.re
    have hA : A.map Complex.ofRealHom = U.val.val := by
      ext i j
      exact Complex.conj_eq_iff_re.mp (hreal i j)
    have hstar : star U.val.val = U.val.val.transpose := by
      ext i j
      exact hreal j i
    have horth : A ∈ Matrix.orthogonalGroup I ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff]
      apply Matrix.map_injective Complex.ofReal_injective
      change Complex.ofRealHom.mapMatrix (A * A.transpose) = Complex.ofRealHom.mapMatrix 1
      rw [map_mul, map_one]
      change A.map Complex.ofRealHom * A.transpose.map Complex.ofRealHom = 1
      rw [Matrix.transpose_map, hA, ← hstar]
      exact U.val.property.2
    refine ⟨⟨A, horth⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hA

/-- A completely degenerate nonzero diagonal form has a full O(n), not just signs. -/
def constantEquiv (r : ℂ) (hr : r ≠ 0) :
    subgroup (fun _ : I => r) ≃* Matrix.orthogonalGroup I ℝ :=
  (MulEquiv.ofBijective (orthogonalHom r hr) (orthogonalHom_bijective r hr)).symm

end
end Math.UnitaryDiagonalCongruence
