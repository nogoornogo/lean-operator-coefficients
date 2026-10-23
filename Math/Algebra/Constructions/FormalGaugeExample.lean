import Math.Algebra.Constructions.FormalGaugeTransformation
import Math.Algebra.Jets.MatrixTraceIBP
import Mathlib.Tactic

/-! A nonconstant polynomial matrix unit, with nonzero pure-gauge connection. -/
namespace Math.FormalGaugeExample
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra FormalConnection MvPolynomial
abbrev Poly := ScalarJetAlgebra.Algebra Unit (Fin 4)
abbrev Mat := Matrix (Fin 2) (Fin 2) Poly
def field : Poly := X ((), 0)
def ordinary : Ordinary (Fin 4) Mat :=
  MatrixTraceIBP.ordinary (totalDerivative (S := Unit) (I := Fin 4)) totalDerivative_commute

def unit : Matˣ where
  val := !![1, field; 0, 1]
  inv := !![1, -field; 0, 1]
  val_inv := by
    apply Matrix.ext
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    apply Matrix.ext
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unit_nonconstant : ordinary.d 0 (unit : Mat) 0 1 ≠ 0 := by
  change totalDerivative 0 field ≠ 0
  simp [field, MvPolynomial.X_ne_zero]

theorem transformed_zero : gauge ordinary (fun _ => (0 : Mat)) unit 0 0 1 =
    -(X ((), Finsupp.single (0 : Fin 4) 1) : Poly) := by
  simp [gauge, ordinary, unit, MatrixTraceIBP.ordinary, Matrix.mul_apply,
    Fin.sum_univ_two, field, ScalarJetAlgebra.shift]

theorem transformed_flat (i j : Fin 4) :
    curvature ordinary (gauge ordinary (fun _ => (0 : Mat)) unit) i j = 0 := by
  rw [gauge_curvature]
  simp [curvature, bracket]

end
end Math.FormalGaugeExample
