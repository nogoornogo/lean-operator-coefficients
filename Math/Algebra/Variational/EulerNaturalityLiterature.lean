import Math.Algebra.Variational.EulerNaturality

/-! Algebraic specialization of Sardanashvily, arXiv:1206.2508v1 (31),(37).
The source supplies notation; these are proved in the actual mixed algebra. -/
namespace Math.GradedEulerComparison
set_option autoImplicit false
noncomputable section
open LocalPolynomial
variable {F B I : Type*}
local instance comparisonDec : DecidableEq (Field F B) := Classical.decEq _
@[reducible] local instance comparisonAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance comparisonModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance comparisonRing : Ring (A F B I) := inferInstance

/-- Formula (31), finite support with unrestricted ordinary-jet order.
The multiindex adjoint is (-D)^alpha; partials are actual left derivatives. -/
theorem multiindex_formula (p : Expr F B I) (s : Field F B) :
    p.euler s = p.gradient.sum (fun j a =>
      if j.1 = s then indexAdjoint j.2 a else 0) := by
  classical
  rw [Expr.euler_eq_eulerMap]
  simp [eulerMap,Finsupp.lsum_apply,Finsupp.sum_apply,Finsupp.single_apply]

theorem actual_partial (p : Expr F B I) (s : Field F B) (a : I →₀ ℕ) :
    p.gradient (s,a) = jetPartial s a p.eval := p.gradient_apply s a

/-- Formula (37), the evolutionary, even-variation specialization with explicit currents. -/
theorem first_variation (p : Expr F B I) (eta : Field F B → A F B I)
    (h : PreservesParity eta) :
    p.variation eta = bulk eta (eulerMap p.gradient) +
      VariationalIBP.divergence D (p.boundary eta) := by
  rw [← Expr.euler_eq_eulerMap]
  exact p.first_variation eta h

end
end Math.GradedEulerComparison
