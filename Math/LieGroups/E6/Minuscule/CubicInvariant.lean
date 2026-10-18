import Math.LieGroups.E6.Minuscule.MatrixNormalizer
import Math.LieAlgebras.SparseCubicCertificate

/-! A nonzero cubic invariant for the actual 27-dimensional Lie action.
All 78 infinitesimal equations are checked over integers in the kernel.
Group invariance is established separately, not assumed here. -/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Math.E6.Minuscule

open SparseCubicCertificate

def cubicCode : Code (Fin 27) := [
  ((0, 12, 26), 1), ((0, 15, 25), -1), ((0, 17, 24), 1),
  ((0, 19, 23), -1), ((0, 21, 22), 1), ((1, 10, 26), -1),
  ((1, 13, 25), 1), ((1, 16, 24), -1), ((1, 18, 23), 1),
  ((1, 20, 22), -1), ((2, 8, 26), 1), ((2, 11, 25), -1),
  ((2, 14, 24), 1), ((2, 18, 21), -1), ((2, 19, 20), 1),
  ((3, 6, 26), -1), ((3, 9, 25), 1), ((3, 14, 23), -1),
  ((3, 16, 21), 1), ((3, 17, 20), -1), ((4, 5, 26), 1),
  ((4, 7, 25), -1), ((4, 14, 22), 1), ((4, 16, 19), -1),
  ((4, 17, 18), 1), ((5, 9, 24), -1), ((5, 11, 23), 1),
  ((5, 13, 21), -1), ((5, 15, 20), 1), ((6, 7, 24), 1),
  ((6, 11, 22), -1), ((6, 13, 19), 1), ((6, 15, 18), -1),
  ((7, 8, 23), -1), ((7, 10, 21), 1), ((7, 12, 20), -1),
  ((8, 9, 22), 1), ((8, 13, 17), -1), ((8, 15, 16), 1),
  ((9, 10, 19), -1), ((9, 12, 18), 1), ((10, 11, 17), 1),
  ((10, 14, 15), -1), ((11, 12, 16), -1), ((12, 13, 14), 1)]

theorem cubic_checked (i : Fin 78) : checkZero (act (LieData.e6Basis i) cubicCode) = true := by
  decide +kernel +revert

noncomputable section

open scoped Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

def cubic : (Fin 27 → ℂ) → ℂ := eval cubicCode

def cubicWitness : Fin 27 → ℂ := fun i => if i = 0 ∨ i = 12 ∨ i = 26 then 1 else 0

theorem cubic_witness : cubic cubicWitness = 1 := by
  norm_num [cubic, cubicCode, eval, value, cubicWitness, Fin.ext_iff]

theorem cubic_ne_zero : cubic ≠ 0 := by
  intro h
  exact one_ne_zero (cubic_witness.symm.trans (congrFun h cubicWitness))

theorem cubic_homogeneous (z : ℂ) (v : Fin 27 → ℂ) : cubic (z • v) = z ^ 3 * cubic v :=
  eval_smul cubicCode z v

theorem cubic_infinitesimal (X : Matrix27) (hX : X ∈ matrixLieAlgebra ℂ) (v : Fin 27 → ℂ) :
    differential cubicCode v (X *ᵥ v) = 0 := by
  have hle : (matrixLieAlgebra ℂ).toSubmodule ≤ annihilator (R := ℂ) cubicCode := by
    rw [← matrixLieAlgebra_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact checked_mem_annihilator _ _ (cubic_checked i)
  exact hle hX v

theorem cubic_real_infinitesimal (X : compactMatrixLieAlgebra) (v : Fin 27 → ℂ) :
    differential cubicCode v ((X : Matrix27) *ᵥ v) = 0 :=
  cubic_infinitesimal X ((mem_compactMatrixLieAlgebra X).mp X.property).1 v

end

end Math.E6.Minuscule
