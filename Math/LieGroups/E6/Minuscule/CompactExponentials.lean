import Math.LieGroups.E6.Minuscule.D5Blocks
import Math.LieGroups.Matrix.MatrixDeterminantExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Special-unitary exponentials of the minuscule compact generators

The generated transformations really lie in SU(27). This does not identify
their subgroup (or its closure) with the simply connected compact E6 group.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

/-- All 18 compact simple-root and Cartan generators, with stable coordinates. -/
def compactGenerator : Fin 3 → Fin 6 → Matrix27
  | 0 => compactX
  | 1 => compactY
  | 2 => compactH

theorem compactGenerator_adjoint (k : Fin 3) (i : Fin 6) :
    (compactGenerator k i)ᴴ = -compactGenerator k i := by
  fin_cases k
  · exact compactX_adjoint i
  · exact compactY_adjoint i
  · exact compactH_adjoint i

theorem compactGenerator_trace (k : Fin 3) (i : Fin 6) :
    Matrix.trace (compactGenerator k i) = 0 := by
  fin_cases k
  · exact (compact_generators_traceless i).1
  · exact (compact_generators_traceless i).2.1
  · exact (compact_generators_traceless i).2.2

theorem d5_compact_generators_preserve_gradeSpace (k : Fin 3) (i : Fin 5)
    (q : ℤ) (v : Fin 27 → ℂ) (hv : v ∈ gradeSpace q) :
    compactGenerator k (d5Node i) *ᵥ v ∈ gradeSpace q := by
  apply mulVec_mem_gradeSpace _ _ q v hv
  intro a b hab
  fin_cases k <;>
    simp [compactGenerator, compactX, compactY, compactH,
      raising_off_block i a b hab, lowering_off_block i a b hab,
      cartan_off_block (d5Node i) a b hab]

theorem exp_compactGenerator_mem (k : Fin 3) (i : Fin 6) (t : ℝ) :
    NormedSpace.exp (t • compactGenerator k i) ∈
      Matrix.specialUnitaryGroup (Fin 27) ℂ := by
  let : NormedAlgebra ℚ Matrix27 := NormedAlgebra.restrictScalars ℚ ℂ Matrix27
  let : IsScalarTower ℚ ℂ Matrix27 := IsScalarTower.restrictScalars ℚ ℂ Matrix27
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply skewAdjoint.smul_mem
    exact compactGenerator_adjoint k i
  · rw [MatrixDeterminantExponential.det_exp, Matrix.trace_smul,
      compactGenerator_trace, smul_zero, Complex.exp_zero]

end

end Math.E6.Minuscule
