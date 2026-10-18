import Math.LieGroups.E6.Minuscule.CorootRotations
import Math.LieGroups.E6.Minuscule.TorusCentralizer
import Mathlib.Topology.Homotopy.Path

/-! Based contractions of the actual six simple-coroot loops. No assertion
that these generate the fundamental group of the candidate is made. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Coroot

noncomputable section

open NormedSpace unitInterval
open scoped Matrix Matrix.Norms.L2Operator

def line (X : compactMatrixLieAlgebra) (t : ℝ) : compactIdentityComponent :=
  compactExp (t • X)

@[simp] theorem line_matrix (X : compactMatrixLieAlgebra) (t : ℝ) :
    compactMatrix (line X t) = exp (t • (X : Matrix27)) := compactExp_coe _

@[simp] theorem line_zero (X : compactMatrixLieAlgebra) : line X 0 = 1 := by
  simp [line]

theorem line_continuous (X : compactMatrixLieAlgebra) : Continuous (line X) :=
  compactExp_continuous.comp (continuous_id.smul continuous_const)

theorem line_add (X : compactMatrixLieAlgebra) (s t : ℝ) :
    line X (s + t) = line X s * line X t := by
  let := NormedAlgebra.restrictScalars ℚ ℂ Matrix27
  apply compactMatrix_injective
  simp only [compactMatrix_mul, line_matrix, add_smul]
  exact exp_add_of_commute (((Commute.refl (X : Matrix27)).smul_left s).smul_right t)

def xLine (i : Fin 6) : ℝ → compactIdentityComponent :=
  line (compactMatrixEquiv (compactGeneratorElement 0 i))

def hLine (i : Fin 6) : ℝ → compactIdentityComponent :=
  line (compactMatrixEquiv (compactGeneratorElement 2 i))

@[simp] theorem xLine_matrix (i : Fin 6) (t : ℝ) :
    compactMatrix (xLine i t) = exp (t • compactX i) := line_matrix _ _

@[simp] theorem hLine_matrix (i : Fin 6) (t : ℝ) :
    compactMatrix (hLine i t) = exp (t • compactH i) := line_matrix _ _

@[simp] theorem xLine_zero (i : Fin 6) : xLine i 0 = 1 := line_zero _
@[simp] theorem hLine_zero (i : Fin 6) : hLine i 0 = 1 := line_zero _

theorem xLine_continuous (i : Fin 6) : Continuous (xLine i) := line_continuous _
theorem hLine_continuous (i : Fin 6) : Continuous (hLine i) := line_continuous _

theorem hLine_add (i : Fin 6) (s t : ℝ) :
    hLine i (s + t) = hLine i s * hLine i t := line_add _ _ _

theorem hLine_torus (i : Fin 6) (t : ℝ) :
    hLine i t = Torus.hom (Torus.phase (Pi.single i t)) := by
  apply compactMatrix_injective
  rw [hLine_matrix, Torus.hom_matrix, ← Torus.exp_direction, Torus.direction_single]

@[simp] theorem hLine_two_pi (i : Fin 6) : hLine i (2 * Real.pi) = 1 := by
  apply compactMatrix_injective
  rw [hLine_matrix, compactMatrix_one, exp_h_two_pi]

theorem hLine_pi_square (i : Fin 6) : hLine i Real.pi * hLine i Real.pi = 1 := by
  rw [← hLine_add, ← two_mul, hLine_two_pi]

theorem hLine_pi_commutes (i : Fin 6) (t : ℝ) :
    Commute (hLine i Real.pi) (xLine i t) := by
  apply compactMatrix_injective
  simp only [compactMatrix_mul, hLine_matrix, xLine_matrix]
  exact (half_period_commutes i t).eq

theorem hLine_quarter_turn (i : Fin 6) (t : ℝ) :
    hLine i t * xLine i (Real.pi / 2) * hLine i t = xLine i (Real.pi / 2) := by
  apply compactMatrix_injective
  simp only [compactMatrix_mul, hLine_matrix, xLine_matrix]
  exact quarter_turn i t

/-- A full coordinate circle in the actual maximal torus. -/
def loop (i : Fin 6) : Path (1 : compactIdentityComponent) 1 where
  toFun t := hLine i (2 * Real.pi * (t : ℝ))
  continuous_toFun := (hLine_continuous i).comp (by fun_prop)
  source' := by simp
  target' := by simp

/-- The fourth factor fixes the basepoint throughout the contraction. -/
def filling (i : Fin 6) (u s : ℝ) : compactIdentityComponent :=
  hLine i (s * Real.pi) * xLine i (u * (Real.pi / 2)) *
    hLine i (s * Real.pi) * (xLine i (u * (Real.pi / 2)))⁻¹

theorem filling_continuous (i : Fin 6) : Continuous (fun p : ℝ × ℝ => filling i p.1 p.2) := by
  unfold filling
  exact ((((hLine_continuous i).comp (by fun_prop)).mul
    ((xLine_continuous i).comp (by fun_prop))).mul
      ((hLine_continuous i).comp (by fun_prop))).mul
        (((xLine_continuous i).comp (by fun_prop)).inv)

theorem filling_start (i : Fin 6) (s : ℝ) : filling i 0 s = hLine i (2 * Real.pi * s) := by
  simp only [filling, zero_mul, xLine_zero, mul_one, inv_one, ← hLine_add]
  congr 1
  ring

theorem filling_finish (i : Fin 6) (s : ℝ) : filling i 1 s = 1 := by
  simp only [filling, one_mul, hLine_quarter_turn, mul_inv_cancel]

theorem filling_source (i : Fin 6) (u : ℝ) : filling i u 0 = 1 := by
  simp [filling]

theorem filling_target (i : Fin 6) (u : ℝ) : filling i u 1 = 1 := by
  simp only [filling, one_mul]
  rw [(hLine_pi_commutes i _).eq,
    mul_assoc (xLine i _) (hLine i Real.pi) (hLine i Real.pi),
    hLine_pi_square, mul_one, mul_inv_cancel]

set_option backward.isDefEq.respectTransparency true in
/-- An actual homotopy, with both loop endpoints fixed at the identity. -/
def contraction (i : Fin 6) : (loop i).Homotopy (Path.refl 1) where
  toFun := (fun p : ℝ × ℝ => filling i p.1 p.2) ∘
    (fun p : I × I => ((p.1 : ℝ), (p.2 : ℝ)))
  continuous_toFun := by
    have hc : Continuous (fun p : I × I => ((p.1 : ℝ), (p.2 : ℝ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact Continuous.comp (filling_continuous i) hc
  map_zero_left s := by
    change filling i 0 (s : ℝ) = hLine i (2 * Real.pi * (s : ℝ))
    exact filling_start i s
  map_one_left s := by
    change filling i 1 (s : ℝ) = 1
    exact filling_finish i s
  prop' u s hs := by
    rcases hs with h | h
    · subst s
      change filling i (u : ℝ) 0 = (loop i) 0
      rw [Path.source]
      exact filling_source i (u : ℝ)
    · rw [Set.mem_singleton_iff] at h
      subst s
      change filling i (u : ℝ) 1 = (loop i) 1
      rw [Path.target]
      exact filling_target i (u : ℝ)

theorem loop_nullhomotopic (i : Fin 6) : (loop i).Homotopic (Path.refl 1) := ⟨contraction i⟩

end

end Math.E6.Minuscule.Coroot
