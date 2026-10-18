import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Multiplicity matrices in block coordinates

On a block with `m` copies of an `n`-dimensional constituent, the multiplicity
matrix acts as `A tensor I_n`. Its determinant is `det(A)^n`, not `det(A)`.
This coordinate construction does not assert that an arbitrary algebraic
isotypic decomposition is orthogonal.
-/

namespace Math.MultiplicityMatrix

noncomputable section

open scoped Kronecker

section Determinant

variable {I : Type*} [Fintype I] [LinearOrder I]
  {n : I → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  {R : Type*} [CommRing R]

/-- The determinant formula also holds for blocks of different sizes. -/
theorem det_blockDiagonal' (A : ∀ i, Matrix (n i) (n i) R) :
    (Matrix.blockDiagonal' A).det = ∏ i, (A i).det := by
  have h : (Matrix.blockDiagonal' A).BlockTriangular Sigma.fst := by
    intro i j hij
    exact Matrix.blockDiagonal'_apply_ne A i.2 j.2 (ne_of_gt hij)
  rw [h.det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e : n i ≃ {x : Sigma n // x.1 = i} :=
    { toFun := fun x => ⟨⟨i, x⟩, rfl⟩
      invFun := fun x => x.2 ▸ x.1.2
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨j, x⟩, rfl⟩; rfl }
  rw [← Matrix.det_reindex_self e.symm]
  congr 1
  ext x y
  exact Matrix.blockDiagonal'_apply_eq A i x y

end Determinant

variable {I : Type*} [Fintype I] [DecidableEq I] (m n : I → ℕ)

abbrev Coordinates := Σ i, Fin (m i) × Fin (n i)

/-- The action of multiplicity matrices on all constituent copies. -/
def amplify (A : Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Matrix (Coordinates m n) (Coordinates m n) ℂ :=
  Matrix.blockDiagonal' fun i => A i ⊗ₖ (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ)

omit [Fintype I] in
@[simp]
theorem amplify_one : amplify m n 1 = 1 := by
  simp only [amplify, Pi.one_apply, Matrix.one_kronecker_one]
  convert (Matrix.blockDiagonal'_one
    (m' := fun i => Fin (m i) × Fin (n i)) (α := ℂ)) using 1

theorem amplify_mul (A B : Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    amplify m n (A * B) = amplify m n A * amplify m n B := by
  simp only [amplify, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  simpa using Matrix.mul_kronecker_mul (A i) (B i)
    (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) 1

omit [Fintype I] in
@[simp]
theorem amplify_star (A : Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    amplify m n (star A) = star (amplify m n A) := by
  simp [amplify, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

omit [Fintype I] in
/-- A zero-dimensional constituent would hide its multiplicity action. -/
theorem amplify_injective (hn : ∀ i, 0 < n i) : Function.Injective (amplify m n) := by
  intro A B h
  funext i x y
  have he := congrArg
    (fun T => T ⟨i, x, ⟨0, hn i⟩⟩ ⟨i, y, ⟨0, hn i⟩⟩) h
  simpa [amplify, Matrix.kroneckerMap_apply] using he

theorem amplify_mem_unitary_iff (hn : ∀ i, 0 < n i)
    (A : Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    amplify m n A ∈ Matrix.unitaryGroup (Coordinates m n) ℂ ↔
      ∀ i, A i ∈ Matrix.unitaryGroup (Fin (m i)) ℂ := by
  simp only [Matrix.mem_unitaryGroup_iff']
  rw [← amplify_star, ← amplify_mul, ← amplify_one m n]
  exact (amplify_injective m n hn).eq_iff.trans (funext_iff)

theorem det_amplify [LinearOrder I]
    (A : Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (amplify m n A).det = ∏ i, (A i).det ^ n i := by
  unfold amplify
  convert (det_blockDiagonal' (fun i => A i ⊗ₖ
    (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ))) using 1
  · congr 2
    exact Subsingleton.elim _ _
  · simp [Matrix.det_kronecker]

/-- Each unitary multiplicity matrix acts unitarily on its copies. -/
def unitaryMap :
    (Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) →*
      Matrix.unitaryGroup (Coordinates m n) ℂ where
  toFun A := ⟨amplify m n (fun i => A i), by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [← amplify_star, ← amplify_mul, ← amplify_one m n]
    congr 1
    funext i
    exact (A i).2.1⟩
  map_one' := Subtype.ext (amplify_one m n)
  map_mul' A B := Subtype.ext (amplify_mul m n (fun i => A i) (fun i => B i))

theorem unitaryMap_injective (hn : ∀ i, 0 < n i) :
    Function.Injective (unitaryMap m n) := by
  intro A B h
  have he : amplify m n (fun i => (A i : Matrix (Fin (m i)) (Fin (m i)) ℂ)) =
      amplify m n (fun i => (B i : Matrix (Fin (m i)) (Fin (m i)) ℂ)) :=
    congrArg (fun u : Matrix.unitaryGroup (Coordinates m n) ℂ =>
      (u : Matrix (Coordinates m n) (Coordinates m n) ℂ)) h
  have hab := amplify_injective m n hn he
  funext i
  exact Subtype.ext (congrFun hab i)

/-- The SU constraint is a weighted determinant character on the product. -/
def weightedDet : (Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) →* ℂ where
  toFun A := ∏ i, (A i : Matrix (Fin (m i)) (Fin (m i)) ℂ).det ^ n i
  map_one' := by simp
  map_mul' A B := by simp [Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]

def specialMultiplicityGroup : Subgroup (Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) :=
  (weightedDet m n).ker

theorem mem_specialMultiplicityGroup_iff [LinearOrder I]
    (A : Π i, Matrix.unitaryGroup (Fin (m i)) ℂ) :
    A ∈ specialMultiplicityGroup m n ↔
      (unitaryMap m n A : Matrix (Coordinates m n) (Coordinates m n) ℂ).det = 1 := by
  change (∏ i, (A i : Matrix (Fin (m i)) (Fin (m i)) ℂ).det ^ n i) = 1 ↔ _
  rw [show (unitaryMap m n A : Matrix (Coordinates m n) (Coordinates m n) ℂ) =
    amplify m n (fun i => A i) from rfl, det_amplify]

omit [Fintype I] in
theorem continuous_amplify : Continuous (amplify m n) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  simp only [amplify, Matrix.blockDiagonal'_apply]
  split_ifs
  · simp only [Matrix.kroneckerMap_apply]
    fun_prop
  · fun_prop

theorem continuous_unitaryMap : Continuous (unitaryMap m n) := by
  apply Continuous.subtype_mk
  exact (continuous_amplify m n).comp
    (continuous_pi fun i => (continuous_apply i).subtype_val)

omit [DecidableEq I] in
theorem continuous_weightedDet : Continuous (weightedDet m n) := by
  change Continuous (fun A : Π i, Matrix.unitaryGroup (Fin (m i)) ℂ =>
    ∏ i, (A i : Matrix (Fin (m i)) (Fin (m i)) ℂ).det ^ n i)
  fun_prop

omit [DecidableEq I] in
theorem isClosed_specialMultiplicityGroup :
    IsClosed (specialMultiplicityGroup m n : Set (Π i, Matrix.unitaryGroup (Fin (m i)) ℂ)) :=
  isClosed_eq (continuous_weightedDet m n) continuous_const

end

end Math.MultiplicityMatrix
