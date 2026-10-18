import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RepresentationTheory.Invariants

/-! Polynomial covariants in supplied finite coordinates evaluate into the
actual stabilizer's fixed space. No generic saturation premise is used. -/
namespace Math.PolynomialCovariantEvaluation
set_option autoImplicit false
noncomputable section
open Representation
variable {H I J : Type*} [Group H]
  (a : Representation ℂ H (I → ℂ)) (b : Representation ℂ H (J → ℂ))

abbrev Polynomials := J → MvPolynomial I ℂ

def evaluate (s : I → ℂ) : Polynomials (I := I) (J := J) →ₗ[ℂ] (J → ℂ) :=
  LinearMap.pi fun j => (MvPolynomial.aeval s).toLinearMap.comp (LinearMap.proj j)

@[simp] theorem evaluate_apply (p : Polynomials (I := I) (J := J)) (s : I → ℂ) (j : J) :
    evaluate s p j = MvPolynomial.eval s (p j) := rfl

/-- Covariance is an independently imposed property of coordinate polynomials. -/
def covariants : Submodule ℂ (Polynomials (I := I) (J := J)) where
  carrier := {p | ∀ g s, evaluate (a g s) p = b g (evaluate s p)}
  zero_mem' := by intro g s; simp
  add_mem' := by intro p q hp hq g s; simp only [map_add, hp g s, hq g s]
  smul_mem' := by intro z p hp g s; simp only [map_smul, hp g s]

def stabilizer (s : I → ℂ) : Subgroup H where
  carrier := {g | a g s = s}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change a (g * h) s = s
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change a g⁻¹ s = s
    have h := congrArg (fun v => a g⁻¹ v) hg
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- This image containment is valid at every value, including exceptional ones. -/
def evaluation (s : I → ℂ) : covariants a b →ₗ[ℂ]
    Representation.invariants (b.comp (stabilizer a s).subtype) where
  toFun p := ⟨evaluate s p.val, by
    rw [Representation.mem_invariants]
    intro g
    have h := p.property g.val s
    rw [g.property] at h
    exact h.symm⟩
  map_add' p q := Subtype.ext ((evaluate s).map_add p.val q.val)
  map_smul' z p := Subtype.ext ((evaluate s).map_smul z p.val)

/-- Constants saturate a trivial target, regardless of the source value. -/
def constant (v : J → ℂ) : covariants a (trivial ℂ H (J → ℂ)) :=
  ⟨fun j => MvPolynomial.C (v j), by
    intro g s
    funext j
    simp [evaluate_apply]⟩

theorem trivial_target_surjective (s : I → ℂ) :
    Function.Surjective (evaluation a (trivial ℂ H (J → ℂ)) s) := by
  intro v
  refine ⟨constant a v.val, ?_⟩
  apply Subtype.ext
  funext j
  simp [evaluation, constant, evaluate_apply]

section ScalarControl
abbrev scalarAction : Representation ℂ ℂˣ (Unit → ℂ) where
  toFun g := (g : ℂ) • LinearMap.id
  map_one' := by ext v i; simp
  map_mul' g h := by ext v i; simp [mul_smul, mul_comm]

/-- A degree-one covariant, with a proved action law. -/
def coordinate : covariants scalarAction scalarAction :=
  ⟨fun _ => MvPolynomial.X (), by
    intro g s
    funext i
    simp [evaluate_apply, scalarAction]⟩

theorem scalar_nonzero_surjective (s : Unit → ℂ) (hs : s () ≠ 0) :
    Function.Surjective (evaluation scalarAction scalarAction s) := by
  intro v
  refine ⟨(v.val () / s ()) • coordinate, ?_⟩
  apply Subtype.ext
  funext i
  cases i
  simp [evaluation, coordinate, evaluate, hs]

/-- At the exceptional zero value, all scalar-weight-one covariants evaluate
 to zero. This does not follow from generic module rank. -/
theorem scalar_zero_evaluation (p : covariants scalarAction scalarAction) :
    evaluate (0 : Unit → ℂ) p.val = 0 := by
  have h := p.property (-1) 0
  have he : evaluate (0 : Unit → ℂ) p.val = -evaluate (0 : Unit → ℂ) p.val := by
    simpa [scalarAction] using h
  funext i
  have hi := congrFun he i
  change evaluate 0 p.val i = -evaluate 0 p.val i at hi
  change evaluate 0 p.val i = 0
  have hz : (2 : ℂ) * evaluate 0 p.val i = 0 := by
    calc
      (2 : ℂ) * evaluate 0 p.val i = evaluate 0 p.val i + evaluate 0 p.val i := by ring
      _ = 0 := by
        linear_combination hi
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
end ScalarControl
end
end Math.PolynomialCovariantEvaluation
