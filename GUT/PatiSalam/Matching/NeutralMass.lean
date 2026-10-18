import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! Exact one-generation neutral mass columns. No finite-mu spectral approximation. -/
namespace GUT.PatiSalam.NeutralMass
set_option autoImplicit false
noncomputable section

def mass (d M mu : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![0,d,0; d,0,M; 0,M,mu]
def mode (d M : ℂ) : Fin 3 → ℂ := ![1,0,-d/M]

theorem mass_symmetric (d M mu : ℂ) : (mass d M mu).transpose = mass d M mu := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exact_zero_mode (d M : ℂ) (hM : M ≠ 0) :
    (mass d M 0).mulVec (mode d M) = 0 := by
  ext i
  fin_cases i <;> simp [mass, mode, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp
  ring

theorem mode_nonzero (d M : ℂ) : mode d M ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [mode] at this

/-- Away from mu=0, this exact massless line need not survive. -/
theorem finite_mu_residual (d M mu : ℂ) (hM : M ≠ 0) :
    (mass d M mu).mulVec (mode d M) = ![0,0,-mu*d/M] := by
  ext i
  fin_cases i <;> simp [mass, mode, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · field_simp; ring
  · ring

/-- The entire exact mass kernel, not just one guessed zero vector. -/
theorem kernel_iff (d M : ℂ) (hM : M ≠ 0) (x : Fin 3 → ℂ) :
    (mass d M 0).mulVec x = 0 ↔ x = x 0 • mode d M := by
  constructor
  · intro hz
    have h1 := congrFun hz 2
    have h2 := congrFun hz 1
    simp [mass, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1 h2
    have hx1 : x 1 = 0 := h1.resolve_left hM
    ext i
    fin_cases i
    · simp [mode]
    · simp [mode, hx1]
    · change x 2 = x 0 * (-d/M)
      apply (mul_left_cancel₀ hM)
      field_simp
      linear_combination h2
  · intro hx
    rw [hx, Matrix.mulVec_smul, exact_zero_mode d M hM]
    simp

end
end GUT.PatiSalam.NeutralMass
