import TauCeti.Algebra.Lie.E6.Minuscule.Basic
import TauCeti.Algebra.Lie.Matrix.IntegralCast
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic

/-!
# Adjoint relations for the pinned minuscule matrices

These are concrete matrices on the standard Hermitian space `Fin 27 → ℂ`.
The skew-Hermitian generators are candidates for a compact real realization;
this file does not identify their generated Lie algebra or a compact E6 group.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

open TauCeti.E6Minuscule
open scoped Matrix

noncomputable section

abbrev Matrix27 := Matrix (Fin 27) (Fin 27) ℂ

def raising (i : Fin 6) : Matrix27 := TauCeti.matrixIntCastLieHom ℂ (raisingMatrix i)
def lowering (i : Fin 6) : Matrix27 := TauCeti.matrixIntCastLieHom ℂ (loweringMatrix i)
def cartan (i : Fin 6) : Matrix27 := TauCeti.matrixIntCastLieHom ℂ (cartanGeneratorMatrix i)

theorem raisingMatrix_transpose (i : Fin 6) : (raisingMatrix i)ᵀ = loweringMatrix i := by
  simp only [raisingMatrix, loweringMatrix, TauCeti.MinusculeWeightTable.raisingMatrix,
    TauCeti.MinusculeWeightTable.loweringMatrix, PEquiv.toMatrix_symm,
    Matrix.transpose_transpose]

@[simp] theorem raising_adjoint (i : Fin 6) : (raising i)ᴴ = lowering i := by
  ext a b
  simpa [raising, lowering, Matrix.conjTranspose_apply] using
    congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M a b : ℂ))
      (raisingMatrix_transpose i)

@[simp] theorem lowering_adjoint (i : Fin 6) : (lowering i)ᴴ = raising i := by
  rw [← raising_adjoint, Matrix.conjTranspose_conjTranspose]

@[simp] theorem cartan_adjoint (i : Fin 6) : (cartan i)ᴴ = cartan i := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [cartan, Matrix.conjTranspose_apply]
  · simp [cartan, Matrix.conjTranspose_apply, h, Ne.symm h]

/-- The real antisymmetric simple-root generator. -/
def compactX (i : Fin 6) : Matrix27 := raising i - lowering i

/-- The imaginary symmetric simple-root generator. -/
def compactY (i : Fin 6) : Matrix27 := Complex.I • (raising i + lowering i)

/-- The imaginary diagonal Cartan generator. -/
def compactH (i : Fin 6) : Matrix27 := Complex.I • cartan i

theorem compactX_adjoint (i : Fin 6) : (compactX i)ᴴ = -compactX i := by
  simp [compactX, Matrix.conjTranspose_sub, neg_sub]

theorem compactY_adjoint (i : Fin 6) : (compactY i)ᴴ = -compactY i := by
  simp [compactY, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

theorem compactH_adjoint (i : Fin 6) : (compactH i)ᴴ = -compactH i := by
  simp [compactH, Matrix.conjTranspose_smul]

theorem integral_traces (i : Fin 6) :
    Matrix.trace (raisingMatrix i) = 0 ∧ Matrix.trace (loweringMatrix i) = 0 ∧
      Matrix.trace (cartanGeneratorMatrix i) = 0 := by
  decide +kernel +revert

theorem trace_intCast (M : Matrix (Fin 27) (Fin 27) ℤ) :
    Matrix.trace (TauCeti.matrixIntCastLieHom ℂ M) = (↑(Matrix.trace M) : ℂ) := by
  simp [Matrix.trace, Matrix.diag, Int.cast_sum]

@[simp] theorem raising_trace (i : Fin 6) : Matrix.trace (raising i) = 0 := by
  simp [raising, trace_intCast, (integral_traces i).1]

@[simp] theorem lowering_trace (i : Fin 6) : Matrix.trace (lowering i) = 0 := by
  simp [lowering, trace_intCast, (integral_traces i).2.1]

@[simp] theorem cartan_trace (i : Fin 6) : Matrix.trace (cartan i) = 0 := by
  simp [cartan, trace_intCast, (integral_traces i).2.2]

theorem compact_generators_traceless (i : Fin 6) :
    Matrix.trace (compactX i) = 0 ∧ Matrix.trace (compactY i) = 0 ∧
      Matrix.trace (compactH i) = 0 := by
  simp [compactX, compactY, compactH, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul]

end

end Math.E6.Minuscule
