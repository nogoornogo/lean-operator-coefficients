import Math.Algebra.Jets.MixedJetPartial
import Math.Algebra.Jets.JetWordAdjoint

/-! The computed Euler family descends from syntax to the actual density.
No normal form or externally supplied equivalence of expressions is assumed. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
variable {F B I : Type*}
@[reducible] local instance semanticAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance semanticModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance semanticRing : Ring (A F B I) := inferInstance
local instance semanticDecF : DecidableEq F := Classical.decEq _
local instance semanticDecB : DecidableEq B := Classical.decEq _
local instance semanticDecI : DecidableEq I := Classical.decEq _

abbrev JetIndex (F B I : Type*) := Field F B × (I →₀ ℕ)
abbrev Gradient (F B I : Type*) := JetIndex F B I →₀ A F B I

def gradientTerms : List (Term F B I) → Gradient F B I
  | [] => 0
  | t::ts => Finsupp.single (t.field, Expr.wordIndex t.derivatives) t.coefficient + gradientTerms ts

@[simp] theorem gradientTerms_append (ts us : List (Term F B I)) :
    gradientTerms (ts++us) = gradientTerms ts+gradientTerms us := by
  induction ts with
  | nil => simp [gradientTerms]
  | cons t ts ih => simp only [List.cons_append, gradientTerms, ih, add_assoc]

theorem gradientTerms_right (ts : List (Term F B I)) (q : A F B I) (j : JetIndex F B I) :
    gradientTerms (ts.map (fun t => {t with coefficient := t.coefficient*q})) j =
      gradientTerms ts j*q := by
  induction ts with
  | nil => simp [gradientTerms]
  | cons t ts ih =>
    simp only [List.map_cons, gradientTerms, Finsupp.add_apply, ih, add_mul]
    congr 1
    by_cases h : (t.field, Expr.wordIndex t.derivatives) = j <;> simp [h]

theorem gradientTerms_left (ts : List (Term F B I)) (p : A F B I) (j : JetIndex F B I) :
    gradientTerms (ts.map (fun t => {t with coefficient := twist t.field p*t.coefficient})) j =
      twist j.1 p*gradientTerms ts j := by
  induction ts with
  | nil => simp [gradientTerms]
  | cons t ts ih =>
    simp only [List.map_cons, gradientTerms, Finsupp.add_apply, ih, mul_add]
    congr 1
    by_cases h : (t.field, Expr.wordIndex t.derivatives) = j
    · subst j; simp
    · simp [h]

namespace Expr

def gradient (p : Expr F B I) : Gradient F B I := gradientTerms (linearize p)

theorem gradient_apply (p : Expr F B I) (s : Field F B) (a : I →₀ ℕ) :
    p.gradient (s,a) = jetPartial s a p.eval := by
  induction p with
  | constant c =>
    change 0 = jetPartial s a (algebraMap ℂ (A F B I) c)
    exact (partial_constant s a c).symm
  | jet t w =>
    cases t <;> simp [gradient,linearize,gradientTerms,eval,Finsupp.single_apply,
      Prod.ext_iff, eq_comm]
  | add p q hp hq => simp only [gradient,linearize,gradientTerms_append,
      Finsupp.add_apply,eval,map_add] at *; rw [hp,hq]
  | mul p q hp hq =>
    simp only [gradient,linearize,gradientTerms_append,Finsupp.add_apply,
      gradientTerms_right,gradientTerms_left]
    rw [← gradient, ← gradient, hp,hq]
    exact (partial_mul s a p.eval q.eval).symm

theorem gradient_eq_of_eval_eq {p q : Expr F B I} (h : p.eval = q.eval) :
    p.gradient = q.gradient := by
  ext ⟨s,a⟩
  rw [gradient_apply,gradient_apply,h]
end Expr

def eulerMap : Gradient F B I →ₗ[ℂ] (Field F B →₀ A F B I) :=
  Finsupp.lsum ℂ (fun j => (Finsupp.lsingle j.1).comp (indexAdjoint j.2))

@[simp] theorem eulerMap_single (j : JetIndex F B I) (p : A F B I) :
    eulerMap (Finsupp.single j p) = Finsupp.single j.1 (indexAdjoint j.2 p) := by
  simp [eulerMap]

theorem eulerMap_terms (ts : List (Term F B I)) :
    eulerMap (gradientTerms ts) = eulerTerms ts := by
  induction ts with
  | nil => simp [gradientTerms,eulerTerms]
  | cons t ts ih => simp [gradientTerms,eulerTerms,ih,indexAdjoint_word]

namespace Expr
theorem euler_eq_eulerMap (p : Expr F B I) : p.euler = eulerMap p.gradient :=
  (eulerMap_terms (linearize p)).symm

/-- Semantic equality, including odd anticommutation and commuting words,
suffices for equality of the entire computed Euler family. -/
theorem euler_eq_of_eval_eq {p q : Expr F B I} (h : p.eval = q.eval) : p.euler = q.euler := by
  rw [euler_eq_eulerMap,euler_eq_eulerMap,gradient_eq_of_eval_eq h]
end Expr

end
end Math.LocalPolynomial
