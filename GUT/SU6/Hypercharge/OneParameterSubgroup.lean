import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Differentiable one-parameter subgroups of Banach algebras

A multiplicative one-parameter subgroup is determined by its derivative at
zero.  The proof transports the derivative to every time using the subgroup
law, then multiplies by the inverse exponential to obtain a function with
zero derivative.

`HasRealDerivAt` fixes the normed additive structure induced by the normed
ring.  This avoids ambiguity for operator algebras, where Lean can otherwise
find definitionally different routes to the same additive topology.
-/

namespace GUT
namespace OneParameterSubgroup

noncomputable section

open NormedSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Real differentiability with the normed additive structure canonically
induced by the normed ring. -/
def HasRealDerivAt (f : ℝ → A) (D : A) (t : ℝ) : Prop :=
  letI hNormedAdd : NormedAddCommGroup A :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup A := hNormedAdd.toAddCommGroup
  HasDerivAt f D t

/-- The derivative in the pinned real normed structure is unique. -/
theorem HasRealDerivAt.unique
    {f : ℝ → A} {D E : A} {t : ℝ}
    (hD : HasRealDerivAt f D t) (hE : HasRealDerivAt f E t) :
    D = E := by
  letI hNormedAdd : NormedAddCommGroup A :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup A := hNormedAdd.toAddCommGroup
  exact HasDerivAt.unique hD hE

/-- The derivative at zero of a multiplicative one-parameter subgroup
determines its derivative at every time. -/
lemma hasRealDerivAt_everywhere_of_add
    (f : ℝ → A) (D : A)
    (hAdd : ∀ s t, f (s + t) = f s * f t)
    (hDeriv : HasRealDerivAt f D 0) (t : ℝ) :
    HasRealDerivAt f (D * f t) t := by
  letI hNormedAdd : NormedAddCommGroup A :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup A := hNormedAdd.toAddCommGroup
  change HasDerivAt f D 0 at hDeriv
  change HasDerivAt f (D * f t) t
  have hShift : HasDerivAt (fun x : ℝ ↦ f (x - t)) D t := by
    have hInner := (hasDerivAt_id t).sub_const t
    have h := hDeriv.scomp_of_eq t hInner (by simp)
    convert h using 1
    · rfl
    · simp
  have hMul := hShift.mul_const (f t)
  apply hMul.congr_of_eventuallyEq
  filter_upwards [] with x
  rw [← hAdd]
  simp

/-- A differentiable multiplicative one-parameter subgroup of a real Banach
algebra is the exponential of its derivative at zero. -/
theorem eq_exp_of_hasRealDerivAt_zero
    [CompleteSpace A]
    (f : ℝ → A) (D : A)
    (hAdd : ∀ s t, f (s + t) = f s * f t)
    (hZero : f 0 = 1)
    (hDeriv : HasRealDerivAt f D 0) (t : ℝ) :
    f t = exp (t • D) := by
  letI hNormedAdd : NormedAddCommGroup A :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup A := hNormedAdd.toAddCommGroup
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  letI : IsScalarTower ℚ ℝ A := IsScalarTower.restrictScalars ℚ ℝ A
  let g : ℝ → A := (fun s ↦ exp (s • (-D))) * f
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have hExp := hasDerivAt_exp_smul_const (-D) s
    have hF0 : HasRealDerivAt f D 0 := by
      change HasDerivAt f D 0
      exact hDeriv
    have hF0' := hasRealDerivAt_everywhere_of_add f D hAdd hF0 s
    have hF : HasDerivAt f (D * f s) s := by
      exact hF0'
    have hMul := hExp.mul hF
    simpa only [g, neg_mul, mul_neg, mul_assoc, neg_add_cancel] using hMul
  have hConst : g t = g 0 :=
    is_const_of_deriv_eq_zero
      (fun s ↦ (hg s).differentiableAt)
      (fun s ↦ (hg s).deriv) t 0
  have hEquation : exp (t • (-D)) * f t = 1 := by
    simpa [g, hZero] using hConst
  have hLeft := congrArg (fun z : A ↦ exp (t • D) * z) hEquation
  have hCommute : Commute (t • D) (t • (-D)) := by
    simpa only [smul_neg] using ((Commute.refl (t • D)).neg_right)
  rw [← mul_assoc, ← exp_add_of_commute hCommute] at hLeft
  simpa [← add_smul] using hLeft

end

end OneParameterSubgroup
end GUT
