import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyElimination
import Math.LinearAlgebra.Exterior.ExteriorLeftDerivative

/-! The coupled all-order equations are actual left contractions of an
explicit Grassmann quadratic action, and their solution defines a genuine
exterior-algebra substitution. -/
namespace Physics.DevMohapatraHeavyAction
set_option autoImplicit false
noncomputable section
open DevMohapatraHeavyElimination
abbrev W := V × (Fin 4 → ℂ)
abbrev B := ExteriorAlgebra ℂ W

def includeExternal : R →ₐ[ℂ] B := ExteriorAlgebra.map (LinearMap.inl ℂ V (Fin 4 → ℂ))
def heavyVector (i : Fin 4) : W := (0, Pi.basisFun ℂ (Fin 4) i)
def heavy (i : Fin 4) : B := ExteriorAlgebra.ι ℂ (heavyVector i)
def dual (i : Fin 4) : Module.Dual ℂ W :=
  (LinearMap.proj i).comp (LinearMap.snd ℂ V (Fin 4 → ℂ))
def derivative (i : Fin 4) : B →ₗ[ℂ] B := Math.ExteriorLeftDerivative.derivative (dual i)

theorem derivative_mul (i : Fin 4) (x y : B) :
    derivative i (x*y) = derivative i x*y + CliffordAlgebra.involute x*derivative i y :=
  Math.ExteriorLeftDerivative.leibniz (dual i) x y

theorem derivative_external (i : Fin 4) (x : R) : derivative i (includeExternal x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => simp [derivative, Math.ExteriorLeftDerivative.derivative]
  | ι v => simp [derivative, Math.ExteriorLeftDerivative.derivative, includeExternal,
      ExteriorAlgebra.map_apply_ι, dual]
  | mul x y hx hy =>
      rw [map_mul, derivative_mul]
      simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

theorem derivative_heavy (i j : Fin 4) :
    derivative i (heavy j) = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [derivative, Math.ExteriorLeftDerivative.derivative, heavy, dual, heavyVector,
    Pi.basisFun_apply, h]

theorem heavy_odd (i : Fin 4) : CliffordAlgebra.involute (heavy i) = -heavy i :=
  CliffordAlgebra.involute_ι _

def universalAction (m M a b : ℂ) : B :=
  -M • (heavy 0*heavy 1) + star M • (heavy 2*heavy 3) + (a*star a/m) •
    (-heavy 0*heavy 2*includeExternal (cross 1 1)+heavy 0*heavy 3*includeExternal (cross 1 0)+
      heavy 1*heavy 2*includeExternal (cross 0 1)-heavy 1*heavy 3*includeExternal (cross 0 0)) -
    (a*b/m) • (heavy 0*includeExternal (DevMohapatraTreeLevel.current u d s 1)-
      heavy 1*includeExternal (DevMohapatraTreeLevel.current u d s 0)) -
    (star a*star b/m) • (heavy 2*includeExternal (DevMohapatraTreeLevel.current ub db sb 1)-
      heavy 3*includeExternal (DevMohapatraTreeLevel.current ub db sb 0)) +
    includeExternal (constant m b)

def evalLinear (n : Fin 4 → R) : W →ₗ[ℂ] R :=
  (ExteriorAlgebra.ι ℂ).comp (LinearMap.fst ℂ V (Fin 4 → ℂ)) +
    ∑ i, (dual i).smulRight (n i)

theorem evalLinear_odd (n : Fin 4 → R) (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) (w : W) :
    Math.ExteriorOdd.Odd (evalLinear n w) := by
  simp only [Math.ExteriorOdd.Odd] at hn ⊢
  simp [evalLinear, map_sum, hn, CliffordAlgebra.involute_ι, Finset.sum_neg_distrib]
  abel

def evaluate (n : Fin 4 → R) (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) : B →ₐ[ℂ] R :=
  ExteriorAlgebra.lift ℂ ⟨evalLinear n,
    fun w => Math.ExteriorOdd.square_zero _ (evalLinear_odd n hn w)⟩

theorem evaluate_external (n : Fin 4 → R) (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) (x : R) :
    evaluate n hn (includeExternal x) = x := by
  have h : (evaluate n hn).comp includeExternal = AlgHom.id ℂ R := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [evaluate, includeExternal, ExteriorAlgebra.map_apply_ι, evalLinear, dual]
  exact AlgHom.congr_fun h x

theorem evaluate_heavy (n : Fin 4 → R) (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) (i : Fin 4) :
    evaluate n hn (heavy i) = n i := by
  simp [evaluate, heavy, heavyVector, evalLinear, dual, Pi.basisFun_apply]

/-- No supplied derivative equations: differentiate the universal action
first, then substitute an arbitrary odd heavy configuration. -/
theorem differentiated_action (m M a b : ℂ) (n : Fin 4 → R)
    (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) (i : Fin 4) :
    evaluate n hn (derivative i (universalAction m M a b)) = DevMohapatraHeavyElimination.residual m M a b n i := by
  fin_cases i <;>
    simp [universalAction, derivative_mul,
      derivative_external, derivative_heavy, heavy_odd, map_mul,
      evaluate_external, evaluate_heavy, DevMohapatraHeavyElimination.residual]
    <;> module

theorem stationary (m M a b : ℂ) (hM : M ≠ 0) (i : Fin 4) :
    evaluate (solution m M a b) (solution_odd m M a b)
      (derivative i (universalAction m M a b)) = 0 := by
  rw [differentiated_action]
  exact congrFun (DevMohapatraHeavyElimination.stationary m M a b hM) i

/-- Uniqueness for actual left derivatives after genuine exterior substitution. -/
theorem stationary_unique (m M a b : ℂ) (hM : M ≠ 0) (n : Fin 4 → R)
    (hn : ∀ i, Math.ExteriorOdd.Odd (n i))
    (hstationary : ∀ i, evaluate n hn (derivative i (universalAction m M a b)) = 0) :
    n = solution m M a b := by
  apply DevMohapatraHeavyElimination.stationary_unique m M a b hM
  ext i
  rw [← differentiated_action m M a b n hn i]
  exact hstationary i

theorem evaluated_action (m M a b : ℂ) (n : Fin 4 → R)
    (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) :
    evaluate n hn (universalAction m M a b) = action m M a b n := by
  simp [universalAction, action, quadratic, linear, evaluate_external, evaluate_heavy]
  abel

theorem eliminated_action (m M a b : ℂ) (hM : M ≠ 0) :
    evaluate (solution m M a b) (solution_odd m M a b) (universalAction m M a b) =
      (1/2 : ℂ) • linear m a b (solution m M a b) + constant m b := by
  rw [evaluated_action, DevMohapatraHeavyElimination.eliminated_action m M a b hM]

end
end Physics.DevMohapatraHeavyAction
