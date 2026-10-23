import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraLiteratureConvention

/-! Zero-momentum mass-inverse sewing and a bounded conjugate-completion
projection. No S-matrix, full Hermitian-action or source-admission premise. -/
namespace Physics.DevMohapatraExternalLeg
set_option autoImplicit false
noncomputable section
open DevMohapatraTreeLevel
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def massKernel (M : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,-M;M,0]
def massInverse (M : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,1/M;-1/M,0]

theorem inverse_left (M : ℂ) (hM : M ≠ 0) : massInverse M * massKernel M = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [massKernel, massInverse, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> field_simp [hM]

theorem inverse_right (M : ℂ) (hM : M ≠ 0) : massKernel M * massInverse M = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [massKernel, massInverse, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> field_simp [hM]

theorem mass_action (M : ℂ) (n : Fin 2 → A V)
    (h : n 1*n 0 = -(n 0*n 1)) :
    (1/2 : ℂ) • (∑ r, ∑ t, massKernel M r t • (n r*n t)) =
      -M • (n 0*n 1) := by
  simp [massKernel, Fin.sum_univ_two, h, smul_smul]
  module

/-- Cubic sources from the two scalar exchanges, in N0,N1 order. -/
def source (g : ℂ) (u d s : Fin 3 → Fin 2 → V) : Fin 2 → A V :=
  ![-g • (∑ a, ExteriorAlgebra.ι ℂ (u a 1) * downCurrent d s a),
    g • (∑ a, ExteriorAlgebra.ι ℂ (u a 0) * downCurrent d s a)]

/-- The quadratic half counts the two oriented contractions once. -/
def sewn (m M a b : ℂ) (u d s : Fin 3 → Fin 2 → V) : A V :=
  (1/2 : ℂ) • ∑ r, ∑ t, massInverse M r t •
    (source (a*b/m) u d s r * source (a*b/m) u d s t)

theorem sewn_current (m M a b : ℂ) (u d s : Fin 3 → Fin 2 → V) :
    sewn m M a b u d s = ((a*b/m)^2/M) •
      (current u d s 0 * current u d s 1) := by
  have hs0 : source (a*b/m) u d s 0 = -(a*b/m) • current u d s 1 := by
    simp [source, current_color]
  have hs1 : source (a*b/m) u d s 1 = (a*b/m) • current u d s 0 := by
    simp [source, current_color]
  simp only [sewn, Fin.sum_univ_two, hs0, hs1]
  simp [massInverse, smul_smul,
    current_swap u d s 1 0]
  module

theorem sewn_generated (m M a b : ℂ) (u d s : Fin 3 → Fin 2 → V) :
    sewn m M a b u d s = generated m M a b u d s := by
  rw [sewn_current]
  rfl

theorem sewn_uv (m M a b : ℂ) (hm : m ≠ 0) (hM : M ≠ 0)
    (u d s : Fin 3 → Fin 2 → V) :
    uvAction m M a b u d s (nSolution m M a b u d s)
      (chiSolution m a u (nSolution m M a b u d s))
      (chiBarSolution m b d s) = sewn m M a b u d s := by
  rw [uv_sequential_on_shell m M a b hm hM, sewn_generated]

theorem fixed_leg (m M a b : ℂ) :
    probeCoefficient (sewn m M a b probeU probeD probeS) = (a*b/m)^2/M := by
  rw [sewn_current, map_smul, probe_product_evaluation]
  simp

/-- Algebraic paired action with an explicitly supplied conjugate completion.
Barred variables and coefficients are independent; no star dictionary inferred. -/
def completedAction {R : Type*} [Ring R] [Algebra ℂ R]
    (m M Mc a b ac bc : ℂ) (n nc : Fin 2 → R)
    (U D Uc Dc chi chiBar : Fin 3 → R) : R :=
  -M • (n 0*n 1) - Mc • (nc 0*nc 1) + ∑ i,
    (m • (chi i*chiBar i) + a • (U i*chiBar i) + b • (chi i*D i) +
      ac • (chi i*Uc i) + bc • (Dc i*chiBar i))

/-- Barred external vertices vanish, leaving a free conjugate Majorana block. -/
theorem completion_projection_free {R : Type*} [Ring R] [Algebra ℂ R]
    (f : R →ₐ[ℂ] A V) (m M Mc a b ac bc : ℂ) (n nc : Fin 2 → R)
    (U D Uc Dc chi chiBar : Fin 3 → R) (u d s : Fin 3 → Fin 2 → V)
    (hU : ∀ i, f (U i) = nuVertex u (fun r => f (n r)) i)
    (hD : ∀ i, f (D i) = downCurrent d s i)
    (hUc : ∀ i, f (Uc i) = 0) (hDc : ∀ i, f (Dc i) = 0) :
    f (completedAction m M Mc a b ac bc n nc U D Uc Dc chi chiBar) =
      uvAction m M a b u d s (fun r => f (n r))
        (fun i => f (chi i)) (fun i => f (chiBar i)) - Mc • (f (nc 0)*f (nc 1)) := by
  simp only [completedAction, uvAction, Math.AlgebraValuedQuadraticElimination.pairedAction,
    map_add, map_sub, map_smul, map_mul, map_sum, hU, hD, hUc, hDc,
    mul_zero, zero_mul, smul_zero, add_zero]
  abel

/-- Exact projection at zero conjugate heavy variable. This is not proof that
full elimination commutes with projection or that the completion is literal H.c. -/
theorem completion_projection {R : Type*} [Ring R] [Algebra ℂ R]
    (f : R →ₐ[ℂ] A V) (m M Mc a b ac bc : ℂ) (n nc : Fin 2 → R)
    (U D Uc Dc chi chiBar : Fin 3 → R) (u d s : Fin 3 → Fin 2 → V)
    (hnc : ∀ r, f (nc r) = 0)
    (hU : ∀ i, f (U i) = nuVertex u (fun r => f (n r)) i)
    (hD : ∀ i, f (D i) = downCurrent d s i)
    (hUc : ∀ i, f (Uc i) = 0) (hDc : ∀ i, f (Dc i) = 0) :
    f (completedAction m M Mc a b ac bc n nc U D Uc Dc chi chiBar) =
      uvAction m M a b u d s (fun r => f (n r))
        (fun i => f (chi i)) (fun i => f (chiBar i)) := by
  simp [completedAction, uvAction, Math.AlgebraValuedQuadraticElimination.pairedAction,
    hnc, hU, hD, hUc, hDc]

end
end Physics.DevMohapatraExternalLeg
