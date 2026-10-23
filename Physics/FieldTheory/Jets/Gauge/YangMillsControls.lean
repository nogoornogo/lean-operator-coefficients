import Physics.FieldTheory.Jets.Gauge.FormalYangMills

/-! An exact non-Abelian polynomial control: a constant two-matrix connection
detects nonzero curvature and a nonzero off-shell Yang–Mills equation. -/
namespace Physics.FormalYangMills.Controls
set_option autoImplicit false
noncomputable section
open Math Math.FormalConnection

abbrev N := Fin 2

def values (i : Fin 4) : Matrix N N ℂ :=
  if i = 0 then !![0, 1; 0, 0] else if i = 1 then !![0, 0; 1, 0] else 0

def evaluation : OffShell N →ₐ[ℂ] ℂ :=
  ScalarJetAlgebra.constantEvaluation (fun j : Components N => values j.1 j.2.1 j.2.2)

def matrixEvaluation : Mat N →ₐ[ℂ] Matrix N N ℂ := evaluation.mapMatrix

theorem evaluation_derivative (i : Fin 4) (p : OffShell N) : evaluation (D N i p) = 0 :=
  ScalarJetAlgebra.constantEvaluation_derivative _ _ _

theorem evaluation_connection (i : Fin 4) : matrixEvaluation (connection N i) = values i := by
  apply Matrix.ext
  intro a b
  change ScalarJetAlgebra.constantEvaluation
    (fun j : Components N => values j.1 j.2.1 j.2.2) (MvPolynomial.X ((i, a, b), 0)) = values i a b
  exact ScalarJetAlgebra.constantEvaluation_X_zero _ _

theorem evaluation_F (i j : Fin 4) :
    matrixEvaluation (F N i j) = bracket (values i) (values j) := by
  apply Matrix.ext
  intro a b
  change evaluation (D N i (connection N j a b) - D N j (connection N i a b) +
    ((connection N i * connection N j) a b - (connection N j * connection N i) a b)) = _
  simp only [map_add, map_sub, evaluation_derivative, sub_self, zero_add]
  change (matrixEvaluation (connection N i * connection N j) -
    matrixEvaluation (connection N j * connection N i)) a b = _
  rw [map_mul, map_mul, evaluation_connection, evaluation_connection]
  rfl

theorem evaluation_nabla (i : Fin 4) (x : Mat N) :
    matrixEvaluation (nabla N i x) = bracket (values i) (matrixEvaluation x) := by
  apply Matrix.ext
  intro a b
  change evaluation (D N i (x a b) +
    ((connection N i * x) a b - (x * connection N i) a b)) = _
  simp only [map_add, map_sub, evaluation_derivative, zero_add]
  change (matrixEvaluation (connection N i * x) - matrixEvaluation (x * connection N i)) a b = _
  rw [map_mul, map_mul, evaluation_connection]
  rfl

theorem curvature_evaluation : evaluation (F N 0 1 0 0) = 1 := by
  change matrixEvaluation (F N 0 1) 0 0 = 1
  rw [evaluation_F]
  norm_num [values, bracket, Matrix.mul_apply, Fin.sum_univ_two]

theorem equation_evaluation : evaluation (equation N 1 0 1) = -2 := by
  change matrixEvaluation (equation N 1) 0 1 = -2
  simp only [equation, map_sum, map_smul, evaluation_nabla, evaluation_F]
  norm_num [Fin.sum_univ_succ, sign, values, bracket, Matrix.mul_apply]

theorem offShell_equation_nonzero : equation N 1 0 1 ≠ 0 := by
  intro h
  have he := congrArg evaluation h
  rw [equation_evaluation, map_zero] at he
  norm_num at he

theorem onShell_equation_zero : projection N (equation N 1 0 1) = 0 :=
  (DifferentialEquation.projection_eq_zero _ _ _).mpr (equation_mem _ _ _ _)

end
end Physics.FormalYangMills.Controls
