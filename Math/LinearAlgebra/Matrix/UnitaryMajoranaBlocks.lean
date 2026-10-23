import Math.LinearAlgebra.Matrix.UnitaryDiagonalCongruence
import Mathlib.Data.Matrix.Block

/-! Explicit product decomposition of full unitary diagonal congruence groups. -/
namespace Math.UnitaryMajoranaBlocks
set_option autoImplicit false
noncomputable section
open Matrix UnitaryDiagonalCongruence
variable {K : Type*} [Fintype K] [DecidableEq K]
  {J : K → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]

def block (U : Matrix (Σ k, J k) (Σ k, J k) ℂ) (k : K) : Matrix (J k) (J k) ℂ :=
  U.submatrix (Sigma.mk k) (Sigma.mk k)

theorem decomposition (b : K → ℂ) (hb : Function.Injective (fun k => Complex.normSq (b k)))
    (U : subgroup (fun i : Σ k, J k => b i.1)) :
    blockDiagonal' (block U.val.val) = U.val.val := by
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases h : k = l
  · subst l; simp [block, blockDiagonal'_apply]
  · simp only [blockDiagonal'_apply, dite_eq_right h]
    exact (no_mixing _ U.val U.property _ _ (fun he => h (hb he))).symm

def unitaryAssemble (A : ∀ k, unitaryGroup (J k) ℂ) : unitaryGroup (Σ k, J k) ℂ :=
  ⟨blockDiagonal' (fun k => (A k).val), by
      rw [mem_unitaryGroup_iff]
      simp only [star_eq_conjTranspose, blockDiagonal'_conjTranspose,
        ← blockDiagonal'_mul]
      have he : (fun k => (A k).val * ((A k).val)ᴴ) = fun k => 1 := by
        funext k; exact (A k).property.2
      rw [he]
      exact blockDiagonal'_one⟩

def assemble (b : K → ℂ) :
    (∀ k, subgroup (fun _ : J k => b k)) →* subgroup (fun i : Σ k, J k => b i.1) where
  toFun A := ⟨unitaryAssemble (fun k => (A k).val), by
    change Preserves _ (unitaryAssemble (fun k => (A k).val)).val
    rw [entry_iff]
    intro ⟨k, i⟩ ⟨l, j⟩
    by_cases h : k = l
    · subst l
      simpa [unitaryAssemble, blockDiagonal'_apply] using (entry_iff _ (A k).val).mp (A k).property i j
    · simp [unitaryAssemble, blockDiagonal'_apply, h]⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact blockDiagonal'_one
  map_mul' A B := by
    apply Subtype.ext; apply Subtype.ext
    exact blockDiagonal'_mul (fun k => (A k).val.val) (fun k => (B k).val.val)

theorem assemble_bijective (b : K → ℂ)
    (hb : Function.Injective (fun k => Complex.normSq (b k))) :
    Function.Bijective (assemble (J := J) b) := by
  constructor
  · intro A B h
    have he := congrArg (fun U : subgroup (fun i : Σ k, J k => b i.1) => U.val.val) h
    change blockDiagonal' (fun k => (A k).val.val) = blockDiagonal' (fun k => (B k).val.val) at he
    have he' := blockDiagonal'_injective he
    funext k
    apply Subtype.ext; apply Subtype.ext
    exact congrFun he' k
  · intro U
    have hd := decomposition b hb U
    have hun : ∀ k, block U.val.val k ∈ unitaryGroup (J k) ℂ := by
      have he := U.val.property.2
      rw [← hd] at he
      simp only [star_eq_conjTranspose, blockDiagonal'_conjTranspose,
        ← blockDiagonal'_mul, ← blockDiagonal'_one] at he
      have hh := blockDiagonal'_injective he
      intro k
      rw [mem_unitaryGroup_iff]
      exact congrFun hh k
    let A : ∀ k, subgroup (fun _ : J k => b k) := fun k =>
      ⟨⟨block U.val.val k, hun k⟩, (entry_iff _ _).mpr (fun i j =>
        (entry_iff _ U.val).mp U.property ⟨k, i⟩ ⟨k, j⟩)⟩
    refine ⟨A, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact hd

def productEquiv (b : K → ℂ)
    (hb : Function.Injective (fun k => Complex.normSq (b k))) :
    subgroup (fun i : Σ k, J k => b i.1) ≃* (∀ k, subgroup (fun _ : J k => b k)) :=
  (MulEquiv.ofBijective (assemble b) (assemble_bijective b hb)).symm

end
end Math.UnitaryMajoranaBlocks
