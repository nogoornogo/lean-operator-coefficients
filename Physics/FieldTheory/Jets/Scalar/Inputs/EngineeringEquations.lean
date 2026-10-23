import Math.Algebra.Jets.JetEngineeringDegree
import Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM
import Physics.FieldTheory.Jets.Gauge.FormalYangMills

/-! Actual scalar and matrix equation weights in the formal engineering grading. -/
namespace Physics.EngineeringEquations
set_option autoImplicit false
noncomputable section
open Math MvPolynomial

theorem scalar_field : PolynomialScalarEOM.field ∈ JetEngineering.grade Unit (Fin 4) 1 := by
  simpa [JetEngineering.grade, JetEngineering.weight, PolynomialScalarEOM.field,
    MasslessScalarEOM.field, ScalarJetAlgebra.order] using
    MvPolynomial.isWeightedHomogeneous_X ℂ JetEngineering.weight ((), (0 : Fin 4 →₀ ℕ))

theorem scalar_equation (lambda : ℂ) : PolynomialScalarEOM.seed lambda ∈
    JetEngineering.grade Unit (Fin 4) 3 := by
  have h (i : Fin 4) : (X ((), Finsupp.single i 2) : PolynomialScalarEOM.OffShell) ∈
      JetEngineering.grade Unit (Fin 4) 3 := by
    simpa [JetEngineering.grade, JetEngineering.weight, ScalarJetAlgebra.order,
      Finsupp.weight_single] using
      MvPolynomial.isWeightedHomogeneous_X ℂ JetEngineering.weight ((), Finsupp.single i 2)
  have hw : LorentzJetIBP.waveField ∈ JetEngineering.grade Unit (Fin 4) 3 := by
    rw [MasslessScalarEOM.waveField_formula]
    exact ((h 0).sub (h 1)).sub (h 2) |>.sub (h 3)
  apply hw.add
  have hprod := (MvPolynomial.isWeightedHomogeneous_C JetEngineering.weight lambda).mul (scalar_field.pow 3)
  simpa using hprod

variable (N : Type*) [Fintype N] [DecidableEq N]
open FormalYangMills

omit [Fintype N] [DecidableEq N] in
theorem connection_degree (i : Fin 4) (a b : N) :
    connection N i a b ∈ JetEngineering.grade (Components N) (Fin 4) 1 := by
  simpa [connection, JetEngineering.grade, JetEngineering.weight, ScalarJetAlgebra.order] using
    MvPolynomial.isWeightedHomogeneous_X ℂ JetEngineering.weight ((i, a, b), (0 : Fin 4 →₀ ℕ))

theorem curvature_degree (i j : Fin 4) (a b : N) :
    F N i j a b ∈ JetEngineering.grade (Components N) (Fin 4) 2 := by
  change D N i (connection N j a b) - D N j (connection N i a b) +
    ((connection N i * connection N j) a b - (connection N j * connection N i) a b) ∈ _
  exact ((JetEngineering.derivative_homogeneous i (connection_degree N j a b)).sub
    (JetEngineering.derivative_homogeneous j (connection_degree N i a b))).add
      ((JetEngineering.matrix_product_mem _ _ (connection_degree N i) (connection_degree N j) a b).sub
        (JetEngineering.matrix_product_mem _ _ (connection_degree N j) (connection_degree N i) a b))

theorem covariant_degree (i : Fin 4) {k : ℕ} (x : Mat N)
    (hx : ∀ a b, x a b ∈ JetEngineering.grade (Components N) (Fin 4) k) (a b : N) :
    nabla N i x a b ∈ JetEngineering.grade (Components N) (Fin 4) (k + 1) := by
  change D N i (x a b) + ((connection N i * x) a b - (x * connection N i) a b) ∈ _
  apply (JetEngineering.derivative_homogeneous i (hx a b)).add
  have hl : (connection N i * x) a b ∈ JetEngineering.grade (Components N) (Fin 4) (k + 1) := by
    simpa only [Nat.add_comm] using
      JetEngineering.matrix_product_mem _ _ (connection_degree N i) hx a b
  exact hl.sub (JetEngineering.matrix_product_mem _ _ hx (connection_degree N i) a b)

theorem equation_degree (j : Fin 4) (a b : N) :
    equation N j a b ∈ JetEngineering.grade (Components N) (Fin 4) 3 := by
  simp only [equation, Matrix.sum_apply, Matrix.smul_apply]
  exact Submodule.sum_mem _ (fun i _ => (JetEngineering.grade _ _ 3).smul_mem _
    (covariant_degree N i (F N i j) (curvature_degree N i j) a b))

end
end Physics.EngineeringEquations
