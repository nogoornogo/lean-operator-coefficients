import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Basic.Complex.Basic

/-!
# Finite character polynomials and contragredient involution

Distinct complex monoid characters are linearly independent, so evaluation
of integer-coefficient finite sums is faithful. The original namespace is
retained for compatibility; this module has no gauge-group dependencies.
-/

set_option autoImplicit false

namespace Math.AbelianActualSpectrum

noncomputable section

variable {G : Type*} [CommGroup G]

abbrev Polynomial (G : Type*) [CommGroup G] := (G →* ℂ) →₀ ℤ

def eval (p : Polynomial G) (g : G) : ℂ :=
  p.sum fun chi n => (n : ℂ) * chi g

@[simp] theorem eval_single (chi : G →* ℂ) (n : ℤ) (g : G) :
    eval (Finsupp.single chi n) g = (n : ℂ) * chi g := by
  classical
  simp [eval]

@[simp] theorem eval_zero (g : G) : eval (0 : Polynomial G) g = 0 := by
  simp [eval]

def toComplex (p : Polynomial G) : (G →* ℂ) →₀ ℂ :=
  p.mapRange (fun n : ℤ => (n : ℂ)) (by simp)

theorem eval_eq_linearCombination (p : Polynomial G) :
    Finsupp.linearCombination ℂ (fun chi : G →* ℂ => (chi : G → ℂ))
      (toComplex p) = fun g => eval p g := by
  ext g
  rw [Finsupp.linearCombination_apply, toComplex, Finsupp.sum_mapRange_index]
  · simp [eval, Finsupp.sum, Finset.sum_apply]
  · intro chi
    simp

theorem eval_injective (p q : Polynomial G) (h : ∀ g, eval p g = eval q g) :
    p = q := by
  have hc : toComplex p = toComplex q :=
    (linearIndependent_monoidHom G ℂ).finsuppLinearCombination_injective
      (by rw [eval_eq_linearCombination, eval_eq_linearCombination]; exact funext h)
  ext chi
  exact Int.cast_injective (α := ℂ) (by
    simpa [toComplex] using congrArg (fun f : (G →* ℂ) →₀ ℂ => f chi) hc)

@[simp] theorem eval_add (p q : Polynomial G) (g : G) :
    eval (p + q) g = eval p g + eval q g := by
  classical
  exact Finsupp.sum_add_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

@[simp] theorem eval_sub (p q : Polynomial G) (g : G) :
    eval (p - q) g = eval p g - eval q g := by
  simp [eval, Finsupp.sum_sub_index, sub_mul]

/-- Contragredient action on one scalar character. -/
def dualCharacter (chi : G →* ℂ) : G →* ℂ where
  toFun g := chi g⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_comm]

@[simp] theorem dualCharacter_apply (chi : G →* ℂ) (g : G) :
    dualCharacter chi g = chi g⁻¹ := rfl

@[simp] theorem dualCharacter_involutive (chi : G →* ℂ) :
    dualCharacter (dualCharacter chi) = chi := by ext g; simp

def dual (p : Polynomial G) : Polynomial G := Finsupp.mapDomain dualCharacter p

@[simp] theorem dual_apply (p : Polynomial G) (chi : G →* ℂ) :
    dual p chi = p (dualCharacter chi) := by
  have hi : Function.Injective (dualCharacter (G := G)) :=
    Function.Involutive.injective dualCharacter_involutive
  simpa [dual] using Finsupp.mapDomain_apply_of_injective hi p (dualCharacter chi)

theorem eval_dual (p : Polynomial G) (g : G) : eval (dual p) g = eval p g⁻¹ := by
  classical
  unfold dual eval
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; simp [add_mul]

end

end Math.AbelianActualSpectrum
