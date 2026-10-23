import Math.RepresentationTheory.Lagrangian.StandardDensityAction
import Math.Algebra.Variational.LagrangianControls

/-! Independent algebraic controls: semantic signs, all word orders, arbitrary
jet order, and simultaneous non-diagonal component/direction changes. -/
namespace Math.EulerNaturalityControls
set_option autoImplicit false
noncomputable section
open LocalPolynomial LocalPolynomial.Expr CoefficientTransport
variable {F B I : Type*}
@[reducible] local instance controlsAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance controlsModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance controlsRing : Ring (A F B I) := inferInstance

/-- Every semantic zero density has zero generated equations. -/
theorem semantic_zero (p : Expr F B I) (h : p.eval = 0) : p.euler = 0 := by
  have he : p.eval = (constant 0 : Expr F B I).eval := by simpa [eval] using h
  exact (Expr.euler_eq_of_eval_eq he).trans (euler_constant 0)

theorem cancelling (p : Expr F B I) : (p-p).euler = 0 :=
  semantic_zero _ (by simp)

/-- Two words representing the same ordinary derivative remain equal after
any polynomial context with the same evaluated density. -/
theorem commuting_words (s : LocalPolynomial.Field F B) (w v : List I) (h : w.Perm v) :
    (jet s w : Expr F B I).euler = (jet s v).euler := by
  apply Expr.euler_eq_of_eval_eq
  have hi : wordIndex w = wordIndex v := by
    classical
    ext i
    rw [wordIndex_count,wordIndex_count,h.count_eq]
  simp only [eval_jet_generator,hi]

/-- A derivative-word permutation remains valid in a nonlinear density context. -/
theorem commuting_words_context (s : LocalPolynomial.Field F B) (w v : List I)
    (h : w.Perm v) (p q : Expr F B I) :
    (jet s w*p+q).euler = (jet s v*p+q).euler := by
  apply Expr.euler_eq_of_eval_eq
  have hi : wordIndex w = wordIndex v := by
    classical
    ext i
    rw [wordIndex_count,wordIndex_count,h.count_eq]
  simp only [eval_add,eval_mul,eval_jet_generator,hi]

/-- A genuine Grassmann reordering, with arbitrary derivative words. -/
theorem odd_reordering (f g : F) (w v : List I) :
    (jet (.inl f) w * jet (.inl g) v : Expr F B I).euler =
      (-(jet (.inl g) v * jet (.inl f) w)).euler := by
  apply Expr.euler_eq_of_eval_eq
  rw [eval_neg,eval_mul,eval_mul]
  change MixedJetAlgebra.odd (f,wordIndex w)*MixedJetAlgebra.odd (g,wordIndex v) =
    -(MixedJetAlgebra.odd (g,wordIndex v)*MixedJetAlgebra.odd (f,wordIndex w))
  have hs := MixedJetParity.odd_slide (f,wordIndex w)
    (MixedJetAlgebra.odd (B := B) (g,wordIndex v))
  simpa only [MixedJetParity.involute_odd,neg_mul] using hs

/-- No derivative-order cutoff is used in the quadratic check. -/
theorem high_jet_square (b : B) (w : List I) :
    ((jet (.inr b) w : Expr F B I)^2).euler =
      Finsupp.single (.inr b)
        ((2:ℂ) • VariationalIBP.adjoint D w (jet (.inr b) w).eval) := by
  have hp : ((jet (.inr b) w : Expr F B I)^2).eval =
      (jet (.inr b) w*jet (.inr b) w).eval := by rw [eval_pow,eval_mul,pow_two]
  rw [Expr.euler_eq_of_eval_eq hp]
  simp [Expr.euler,linearize,eulerTerms,twist,
    ← two_smul ℂ]

/-- Shears form a group action and mix both component and derivative bases. -/
def shear : Representation ℂ (Multiplicative ℂ) (JetLinear.Field (Fin 2)) where
  toFun t := JetLinear.shear t.toAdd
  map_one' := by ext v j; simp [JetLinear.shear]
  map_mul' t u := by
    ext v j
    simp [JetLinear.shear,add_smul]
    ring

abbrev Change := StandardDensityAction.prolongation shear shear shear

/-- Arbitrary nonlinear densities and arbitrary high jets use the same chain rule. -/
theorem simultaneous_change (p : Expr (Fin 2) (Fin 2) (Fin 2)) (t : Multiplicative ℂ) :
    ((Change t).toLinearSubstitution.expr p).euler =
      push (Change t).fields (Change t).algebra.toLinearMap p.euler :=
  (Change t).euler_natural p _ ((Change t).toLinearSubstitution.eval_expr p)

/-- The direction action really is non-diagonal. -/
theorem direction_mixes : shear (Multiplicative.ofAdd (1:ℂ)) (Finsupp.single 1 1) =
    Finsupp.single 1 1+Finsupp.single 0 1 := by simp [shear,JetLinear.shear_one]

/-- The zero group parameter gives identity Euler transport for every density. -/
theorem zero_change (p : Expr (Fin 2) (Fin 2) (Fin 2)) :
    ((Change 1).toLinearSubstitution.expr p).euler = p.euler := by
  apply Expr.euler_eq_of_eval_eq
  rw [LinearSubstitution.eval_expr]
  change StandardDensityAction.action shear shear shear 1 p.eval = p.eval
  rw [map_one]
  rfl

end
end Math.EulerNaturalityControls
