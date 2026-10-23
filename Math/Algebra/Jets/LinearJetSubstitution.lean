import Math.Algebra.Variational.SemanticEuler
import Math.LinearAlgebra.Selection.CoefficientTransport

/-! Graded chain rule for actual linear substitutions of ordinary jets.
Compatibility is checked on generators, not on Euler expressions. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
open CoefficientTransport
variable {F B I : Type*}
@[reducible] local instance substAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance substModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance substRing : Ring (A F B I) := inferInstance

abbrev JetSpace (F B I : Type*) := JetIndex F B I →₀ ℂ

def generator (j : JetIndex F B I) : A F B I :=
  match j.1 with
  | .inl f => MixedJetAlgebra.odd (f,j.2)
  | .inr b => MixedJetAlgebra.even (b,j.2)

def jetVector : JetSpace F B I →ₗ[ℂ] A F B I := Finsupp.linearCombination ℂ generator

@[simp] theorem jetVector_single (j : JetIndex F B I) (c : ℂ) :
    jetVector (Finsupp.single j c) = c • generator j := by simp [jetVector]

namespace Expr
@[simp] theorem gradient_constant (c : ℂ) : (constant c : Expr F B I).gradient = 0 := rfl
@[simp] theorem gradient_add (p q : Expr F B I) : (p+q).gradient = p.gradient+q.gradient :=
  gradientTerms_append _ _
@[simp] theorem gradient_smul (c : ℂ) (p : Expr F B I) : (c • p).gradient = c • p.gradient := by
  ext ⟨s,a⟩
  simp [gradient_apply]

@[simp] theorem gradient_jet (s : Field F B) (w : List I) :
    (jet s w : Expr F B I).gradient = Finsupp.single (s,wordIndex w) 1 := by
  simp [gradient,linearize,gradientTerms]

@[simp] theorem eval_jet_generator (s : Field F B) (w : List I) :
    (jet s w : Expr F B I).eval = generator (s,wordIndex w) := by cases s <;> rfl

/-- Every finite linear combination of actual jets has a checked syntax representative. -/
theorem exists_linear (v : JetSpace F B I) :
    ∃ p : Expr F B I, p.eval = jetVector v ∧ p.gradient = spread v 1 := by
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨constant 0,by simp [eval],by simp⟩
  | add v w hv hw =>
    obtain ⟨p,hp,dp⟩ := hv
    obtain ⟨q,hq,dq⟩ := hw
    exact ⟨p+q,by simp [hp,hq],by rw [gradient_add,dp,dq,spread_add]⟩
  | single j c =>
    obtain ⟨s,a⟩ := j
    obtain ⟨w,rfl⟩ := wordIndex_surjective a
    refine ⟨c • jet s w,by simp,?_⟩
    simp

def linear (v : JetSpace F B I) : Expr F B I := Classical.choose (exists_linear v)
@[simp] theorem eval_linear (v : JetSpace F B I) : (linear v).eval = jetVector v :=
  (Classical.choose_spec (exists_linear v)).1
@[simp] theorem gradient_linear (v : JetSpace F B I) : (linear v).gradient = spread v 1 :=
  (Classical.choose_spec (exists_linear v)).2
end Expr

def rightMul (q : A F B I) : A F B I →ₗ[ℂ] A F B I where
  toFun p := p*q
  map_add' _ _ := add_mul _ _ _
  map_smul' _ _ := smul_mul_assoc _ _ _

theorem gradient_mul (p q : Expr F B I) :
    (p*q).gradient = diagonal (fun _ => rightMul q.eval) p.gradient +
      diagonal (fun j => leftMul (twist j.1 p.eval)) q.gradient := by
  ext ⟨s,a⟩
  simp [Expr.gradient_apply,partial_mul,rightMul,leftMul]

/-- Action data: an algebra map, its linear jet map, and parity compatibility.
These obligations do not mention the Lagrangian or its Euler family. -/
structure LinearSubstitution (F B I : Type*) where
  algebra : A F B I →ₐ[ℂ] A F B I
  jets : JetSpace F B I →ₗ[ℂ] JetSpace F B I
  generator_map : ∀ j, algebra (generator j) = jetVector (jets (Finsupp.single j 1))
  twist_map : ∀ s p, algebra (twist s p) = twist s (algebra p)
  parity : ∀ j k, jets (Finsupp.single j 1) k ≠ 0 →
    ∀ p : A F B I, twist j.1 p = twist k.1 p

namespace LinearSubstitution
variable (T : LinearSubstitution F B I)

def expr : Expr F B I → Expr F B I
  | .constant c => .constant c
  | .jet s w => Expr.linear (T.jets (Finsupp.single (s,Expr.wordIndex w) 1))
  | .add p q => expr p+expr q
  | .mul p q => expr p*expr q

@[simp] theorem eval_expr (p : Expr F B I) : (T.expr p).eval = T.algebra p.eval := by
  induction p with
  | constant c => exact (T.algebra.commutes c).symm
  | jet s w => simp only [expr,Expr.eval_linear,Expr.eval_jet_generator,T.generator_map]
  | add p q hp hq =>
    change (T.expr p+T.expr q).eval = T.algebra (p+q).eval
    simp only [Expr.eval_add,map_add,hp,hq]
  | mul p q hp hq =>
    change (T.expr p*T.expr q).eval = T.algebra (p*q).eval
    simp only [Expr.eval_mul,map_mul,hp,hq]

def gradientMap := push T.jets T.algebra.toLinearMap

theorem gradientMap_right (q : A F B I) (v : Gradient F B I) :
    T.gradientMap (diagonal (fun _ => rightMul q) v) =
      diagonal (fun _ => rightMul (T.algebra q)) (T.gradientMap v) := by
  have h : T.gradientMap.comp (diagonal (fun _ => rightMul q)) =
      (diagonal (fun _ => rightMul (T.algebra q))).comp T.gradientMap := by
    apply Finsupp.lhom_ext
    intro j a
    ext k
    simp [gradientMap,rightMul]
  exact LinearMap.congr_fun h v

theorem gradientMap_left (p : A F B I) (v : Gradient F B I) :
    T.gradientMap (diagonal (fun j => leftMul (twist j.1 p)) v) =
      diagonal (fun j => leftMul (twist j.1 (T.algebra p))) (T.gradientMap v) := by
  have h : T.gradientMap.comp (diagonal (fun j => leftMul (twist j.1 p))) =
      (diagonal (fun j => leftMul (twist j.1 (T.algebra p)))).comp T.gradientMap := by
    apply Finsupp.lhom_ext
    intro j a
    ext k
    simp only [LinearMap.comp_apply,diagonal_single,gradientMap,push_single,
      spread_apply,diagonal_apply,leftMul,LinearMap.coe_mk,AddHom.coe_mk,
      AlgHom.toLinearMap_apply,map_mul,T.twist_map]
    by_cases hz : T.jets (Finsupp.single j 1) k = 0
    · simp [hz]
    · rw [T.parity j k hz, mul_smul_comm]
  exact LinearMap.congr_fun h v

/-- The graded chain rule is derived by induction from actual algebra/jet data. -/
theorem gradient_expr (p : Expr F B I) : (T.expr p).gradient = T.gradientMap p.gradient := by
  induction p with
  | constant c => simp [expr,gradientMap]
  | jet s w => simp [expr,gradientMap]
  | add p q hp hq =>
    change (T.expr p+T.expr q).gradient = T.gradientMap (p+q).gradient
    simp only [Expr.gradient_add,hp,hq,map_add]
  | mul p q hp hq =>
    change (T.expr p*T.expr q).gradient = T.gradientMap (p*q).gradient
    rw [gradient_mul,gradient_mul,map_add,T.gradientMap_right,T.gradientMap_left,
      hp,hq,T.eval_expr,T.eval_expr]

/-- Naturality for any representative of the transformed evaluated density. -/
theorem gradient_natural (p q : Expr F B I) (hq : q.eval = T.algebra p.eval) :
    q.gradient = T.gradientMap p.gradient := by
  rw [Expr.gradient_eq_of_eval_eq (hq.trans (T.eval_expr p).symm),T.gradient_expr]
end LinearSubstitution

end
end Math.LocalPolynomial
