import Math.LinearAlgebra.Constructions.DiagonalAdjointMass
import GUT.SU5.Representations.CurrentBlocks

open Math

/-! An explicitly supplied adjoint background and its double-commutator
mass operator. This does not select a vacuum or set a physical energy scale. -/

set_option autoImplicit false
namespace GUT.SU5.AdjointMass
noncomputable section
open scoped Matrix

def diagonal (v : ℝ) : Fin 5 → ℂ :=
  ![2 * v, 2 * v, 2 * v, -3 * v, -3 * v]

def background (v : ℝ) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal (diagonal v)

def massOperator (g v : ℝ) (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (g : ℂ) ^ 2 • DiagonalAdjointMass.operator (diagonal v) X

def massSquared (g v : ℝ) : ℝ := 25 * g ^ 2 * v ^ 2

theorem background_trace (v : ℝ) : Matrix.trace (background v) = 0 := by
  simp [background, diagonal, Matrix.trace, Fin.sum_univ_succ]
  ring

theorem background_hermitian (v : ℝ) : (background v)ᴴ = background v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [background, diagonal, Matrix.conjTranspose_apply]

theorem upper_mass (g v : ℝ) (a : Fin 3) (w : Fin 2) :
    massOperator g v (Matrix.single (Fin.castAdd 2 a) (Fin.natAdd 3 w) 1) =
      (massSquared g v : ℂ) • Matrix.single (Fin.castAdd 2 a) (Fin.natAdd 3 w) 1 := by
  rw [massOperator, DiagonalAdjointMass.single_eigenvector, smul_smul]
  congr 1
  fin_cases a <;> fin_cases w <;> simp [diagonal, massSquared] <;> ring

theorem lower_mass (g v : ℝ) (a : Fin 3) (w : Fin 2) :
    massOperator g v (Matrix.single (Fin.natAdd 3 w) (Fin.castAdd 2 a) 1) =
      (massSquared g v : ℂ) • Matrix.single (Fin.natAdd 3 w) (Fin.castAdd 2 a) 1 := by
  rw [massOperator, DiagonalAdjointMass.single_eigenvector, smul_smul]
  congr 1
  fin_cases a <;> fin_cases w <;> simp [diagonal, massSquared] <;> ring

theorem massSquared_pos {g v : ℝ} (hg : g ≠ 0) (hv : v ≠ 0) : 0 < massSquared g v := by
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hg)) (sq_pos_of_ne_zero hv)

theorem massSquared_ne_zero {g v : ℝ} (hg : g ≠ 0) (hv : v ≠ 0) :
    (massSquared g v : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (massSquared_pos hg hv)

theorem degenerate_mass (g v : ℝ) : massSquared 0 v = 0 ∧ massSquared g 0 = 0 := by
  simp [massSquared]

end
end GUT.SU5.AdjointMass
