import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

/-! Continuous real lifts of identity-based circle loops, normalized in
turns. The integral endpoint is derived from the actual exponential cover. -/

set_option autoImplicit false

namespace Math.CircleLoopLift

noncomputable section

open unitInterval

def angle (p : Path (1 : Circle) 1) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath p.toContinuousMap 0 (by simp)

@[simp] theorem angle_zero (p : Path (1 : Circle) 1) : angle p 0 = 0 :=
  Circle.isCoveringMap_exp.liftPath_zero _ _ _

theorem exp_angle (p : Path (1 : Circle) 1) (s : I) : Circle.exp (angle p s) = p s :=
  congrFun (Circle.isCoveringMap_exp.liftPath_lifts p.toContinuousMap 0 (by simp)) s

theorem angle_one_period (p : Path (1 : Circle) 1) :
    ∃ n : ℤ, angle p 1 = (n : ℝ) * (2 * Real.pi) := by
  apply Circle.exp_eq_one.mp
  rw [exp_angle, Path.target]

def turns (p : Path (1 : Circle) 1) : C(I, ℝ) where
  toFun s := angle p s / (2 * Real.pi)
  continuous_toFun := (angle p).continuous.div_const _

@[simp] theorem turns_zero (p : Path (1 : Circle) 1) : turns p 0 = 0 := by
  simp [turns]

theorem exp_turns (p : Path (1 : Circle) 1) (s : I) :
    Circle.exp (2 * Real.pi * turns p s) = p s := by
  change Circle.exp (2 * Real.pi * (angle p s / (2 * Real.pi))) = p s
  rw [mul_div_cancel₀ _ Real.two_pi_pos.ne', exp_angle]

theorem turns_one_integer (p : Path (1 : Circle) 1) : ∃ n : ℤ, turns p 1 = (n : ℝ) := by
  obtain ⟨n, hn⟩ := angle_one_period p
  refine ⟨n, ?_⟩
  change angle p 1 / (2 * Real.pi) = _
  rw [hn, mul_div_cancel_right₀ _ Real.two_pi_pos.ne']

end

end Math.CircleLoopLift
