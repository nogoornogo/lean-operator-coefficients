import Math.Algebra.Constructions.FormalGaugeTransformation
import Math.Algebra.Jets.MatrixTraceIBP
import Physics.FieldTheory.Jets.Gauge.FormalYangMills

/-! Local unit covariance and trace IBP for the actual matrix jet connection.
This does not construct an automorphism of the connection-only polynomial ring. -/
namespace Physics.FormalYangMills
set_option autoImplicit false
noncomputable section
open Math Math.FormalConnection
variable (N : Type*) [Fintype N] [DecidableEq N]

def transformedConnection (u : (Mat N)ˣ) := gauge (ordinary N) (connection N) u

theorem local_curvature (u : (Mat N)ˣ) (i j : Fin 4) :
    curvature (ordinary N) (transformedConnection N u) i j =
      (u : Mat N) * F N i j * (↑u⁻¹ : Mat N) := gauge_curvature _ _ _ _ _

theorem local_equation (u : (Mat N)ˣ) (j : Fin 4) :
    signedEquation (ordinary N) (transformedConnection N u) sign j =
      (u : Mat N) * equation N j * (↑u⁻¹ : Mat N) := gauge_equation _ _ _ _ _

theorem local_equation_mem (u : (Mat N)ˣ) (j : Fin 4) :
    entriesMem N (signedEquation (ordinary N) (transformedConnection N u) sign j) := by
  rw [local_equation]
  exact entries_mul_right N _ _ (entries_mul_left N _ _ (equation_mem N j))

theorem local_equation_zero (u : (Mat N)ˣ) (j : Fin 4) (a b : N) :
    projection N (signedEquation (ordinary N) (transformedConnection N u) sign j a b) = 0 :=
  (DifferentialEquation.projection_eq_zero _ _ _).mpr (local_equation_mem N u j a b)

theorem trace_local_curvature_square (u : (Mat N)ˣ) (i j : Fin 4) :
    Matrix.trace (curvature (ordinary N) (transformedConnection N u) i j *
      curvature (ordinary N) (transformedConnection N u) i j) = Matrix.trace (F N i j * F N i j) := by
  rw [local_curvature]
  have h : (u : Mat N) * F N i j * (↑u⁻¹ : Mat N) *
      ((u : Mat N) * F N i j * (↑u⁻¹ : Mat N)) =
      (u : Mat N) * (F N i j * F N i j) * (↑u⁻¹ : Mat N) := by
    simp only [mul_assoc, ← mul_assoc (↑u⁻¹ : Mat N) (u : Mat N), Units.inv_mul, one_mul]
  rw [h]
  exact MatrixTraceIBP.trace_conjugate u _

theorem trace_ibp (i : Fin 4) (x y : Mat N) :
    Matrix.trace (nabla N i x * y) + Matrix.trace (x * nabla N i y) =
      D N i (Matrix.trace (x * y)) :=
  MatrixTraceIBP.trace_ibp (D N) ScalarJetAlgebra.totalDerivative_commute (connection N) i x y

theorem trace_ibp_onShell (i : Fin 4) (x y : Mat N) :
    DifferentialEquation.integrated (D N) (equations N) (Matrix.trace (nabla N i x * y)) =
      -DifferentialEquation.integrated (D N) (equations N) (Matrix.trace (x * nabla N i y)) :=
  MatrixTraceIBP.trace_ibp_integrated (D N) ScalarJetAlgebra.totalDerivative_commute
    (connection N) (equations N) i x y

end
end Physics.FormalYangMills
