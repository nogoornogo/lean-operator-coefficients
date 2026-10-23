import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyHermitian

/-! The unique all-order stationary solution respects the concrete Hermitian
field conjugation. Complexifying the four variables does not lose conjugacy. -/
namespace Physics.DevMohapatraHeavyConjugacy
set_option autoImplicit false
noncomputable section
open DevMohapatraHeavyElimination DevMohapatraHeavyAction DevMohapatraHeavyHermitian
open DevMohapatraTreeLevel Math.ExteriorHermitianConjugation

def adj (x : R) : R := adjoint fieldConjugation x

theorem field_involutive (v : V) : fieldConjugation (fieldConjugation v) = v :=
  coordinateConjugation_involutive _ swapExternal_involutive v

theorem adj_involutive (x : R) : adj (adj x) = x := adjoint_involutive _ field_involutive x
theorem adj_mul (x y : R) : adj (x*y) = adj y*adj x := adjoint_mul _ x y
theorem adj_smul (z : ℂ) (x : R) : adj (z • x) = star z • adj x := adjoint_smul _ z x
theorem adj_add (x y : R) : adj (x+y) = adj x+adj y := by simp [adj, adjoint]
theorem adj_sub (x y : R) : adj (x-y) = adj x-adj y := by simp [adj, adjoint]
theorem adj_neg (x : R) : adj (-x) = -adj x := by simp [adj, adjoint]
theorem adj_zero : adj 0 = 0 := by simp [adj, adjoint]

theorem include_adj (x : R) : includeExternal (adj x) = hc (includeExternal x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => simp [adj, adjoint, hc, includeExternal]
  | ι v => simp [adj, adjoint, includeExternal,
      ExteriorAlgebra.map_apply_ι, hc_generator, conjugation]
  | mul x y hx hy => simp only [adj_mul, map_mul, hc_mul, hx, hy]
  | add x y hx hy => simp only [adj_add, map_add, hc_add, hx, hy]

theorem include_injective : Function.Injective includeExternal := by
  have h (x : R) : ExteriorAlgebra.map (LinearMap.fst ℂ V (Fin 4 → ℂ)) (includeExternal x) = x := by
    have hhom : (ExteriorAlgebra.map (LinearMap.fst ℂ V (Fin 4 → ℂ))).comp includeExternal =
        AlgHom.id ℂ R := by
      apply ExteriorAlgebra.hom_ext
      ext v
      simp [includeExternal]
    exact AlgHom.congr_fun hhom x
  exact Function.LeftInverse.injective h

theorem adj_current (r : Fin 2) : adj (current u d s r) = -current ub db sb r := by
  apply include_injective
  rw [include_adj]
  simp only [current_color, map_sum, map_mul, map_neg, hc_sum, hc_mul]
  change (∑ c, hc (D c)*hc (includeExternal (ExteriorAlgebra.ι ℂ (u c r)))) =
    -(∑ c, includeExternal (ExteriorAlgebra.ι ℂ (ub c r))*Db c)
  simp only [hc_D, hc_external_generator, fieldConjugation_u, neg_mul,
    Db_commutes, Finset.sum_neg_distrib]

theorem adj_bar_current (r : Fin 2) : adj (current ub db sb r) = -current u d s r := by
  have h := congrArg adj (adj_current r)
  rw [adj_involutive, adj_neg] at h
  simpa using congrArg Neg.neg h.symm

theorem field_bar_u (c : Fin 3) (r : Fin 2) : fieldConjugation (ub c r) = u c r := by
  rw [← fieldConjugation_u c r, field_involutive]

theorem adj_cross (r t : Fin 2) : adj (cross r t) = cross t r := by
  simp [adj, adjoint, cross, map_sum, map_mul, fieldConjugation_u, field_bar_u]

def conjugated (n : Fin 4 → R) (i : Fin 4) : R := adj (n (swapHeavy i))

theorem residual_conjugated (m M a b : ℂ) (hmreal : star m = m)
    (n : Fin 4 → R) (i : Fin 4) :
    DevMohapatraHeavyElimination.residual m M a b (conjugated n) i =
      -adj (DevMohapatraHeavyElimination.residual m M a b n (swapHeavy i)) := by
  fin_cases i <;>
    simp [DevMohapatraHeavyElimination.residual, conjugated, swapHeavy,
      adj_add, adj_sub, adj_neg, adj_smul, adj_mul, adj_current, adj_bar_current,
      adj_cross, cross_commutes, hmreal, smul_add, smul_sub, smul_neg, neg_mul]
    <;> module

theorem solution_conjugated (m M a b : ℂ) (hM : M ≠ 0) (hmreal : star m = m) :
    conjugated (solution m M a b) = solution m M a b := by
  apply DevMohapatraHeavyElimination.stationary_unique m M a b hM
  ext i
  rw [residual_conjugated m M a b hmreal]
  have h := congrFun (DevMohapatraHeavyElimination.stationary m M a b hM) (swapHeavy i)
  simp only [h, Pi.zero_apply, adj_zero, neg_zero]

theorem solution_adjoint (m M a b : ℂ) (hM : M ≠ 0) (hmreal : star m = m) (i : Fin 4) :
    adj (solution m M a b i) = solution m M a b (swapHeavy i) := by
  have h := congrFun (solution_conjugated m M a b hM hmreal) (swapHeavy i)
  simpa [conjugated, swapHeavy_involutive] using h

theorem adj_generator (v : V) : adj (ExteriorAlgebra.ι ℂ v) =
    ExteriorAlgebra.ι ℂ (fieldConjugation v) := by simp [adj, adjoint]

theorem adj_sum {I : Type*} (t : Finset I) (f : I → R) :
    adj (∑ i ∈ t, f i) = ∑ i ∈ t, adj (f i) := by simp [adj, adjoint, map_sum]

theorem evaluate_conjugate_generator (m M a b : ℂ) (hM : M ≠ 0)
    (hmreal : star m = m) (w : W) :
    evaluate (solution m M a b) (solution_odd m M a b)
      (ExteriorAlgebra.ι ℂ (conjugation w)) =
      adj (evaluate (solution m M a b) (solution_odd m M a b) (ExteriorAlgebra.ι ℂ w)) := by
  simp [evaluate, evalLinear, conjugation, dual, adj_add, adj_smul, adj_generator,
    solution_adjoint m M a b hM hmreal, Fin.sum_univ_succ, heavyConjugation,
    coordinateConjugation, swapHeavy]
  abel

/-- The full stationary substitution preserves the constructed H.c.,
including complex couplings and all heavy corrections. -/
theorem evaluate_hc (m M a b : ℂ) (hM : M ≠ 0) (hmreal : star m = m) (x : B) :
    evaluate (solution m M a b) (solution_odd m M a b) (hc x) =
      adj (evaluate (solution m M a b) (solution_odd m M a b) x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap z => simp [hc, adj, adjoint]
  | ι w =>
    rw [hc_generator]
    exact evaluate_conjugate_generator m M a b hM hmreal w
  | mul x y hx hy => simp only [hc_mul, map_mul, adj_mul, hx, hy]
  | add x y hx hy => simp only [hc_add, map_add, adj_add, hx, hy]

theorem eliminated_hermitian (m M a b : ℂ) (hM : M ≠ 0) (hmreal : star m = m) :
    adj (evaluate (solution m M a b) (solution_odd m M a b) (universalAction m M a b)) =
      evaluate (solution m M a b) (solution_odd m M a b) (universalAction m M a b) := by
  rw [← evaluate_hc m M a b hM hmreal, universal_hermitian m M a b hmreal]

end
end Physics.DevMohapatraHeavyConjugacy
