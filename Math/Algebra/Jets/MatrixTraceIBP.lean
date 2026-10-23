import Math.Algebra.Constructions.FormalConnection
import Math.RepresentationTheory.Jets.NonlinearJetIBP
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Trace cyclicity turns the actual covariant Leibniz identity into ordinary
divergence relations, including after arbitrary polynomial EOM. -/
namespace Math.MatrixTraceIBP
set_option autoImplicit false
noncomputable section
open FormalConnection
variable {A I N : Type*} [CommRing A] [Algebra ℂ A] [Fintype N] [DecidableEq N]
  (D : I → Derivation ℂ A A) (hc : ∀ i j p, D i (D j p) = D j (D i p))

def ordinary : Ordinary I (Matrix N N A) where
  d i := (D i).toLinearMap.mapMatrix
  mul i x y := by
    apply Matrix.ext
    intro a b
    change D i (∑ k, x a k * y k b) = (∑ k, D i (x a k) * y k b) + ∑ k, x a k * D i (y k b)
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [smul_eq_mul, mul_comm, add_comm] using (D i).leibniz (x a k) (y k b)
  commute i j x := by
    apply Matrix.ext
    intro a b
    exact hc i j (x a b)

omit [Algebra ℂ A] in
theorem trace_bracket (x y : Matrix N N A) : Matrix.trace (bracket x y) = 0 := by
  rw [bracket, Matrix.trace_sub, Matrix.trace_mul_comm x y, sub_self]

theorem trace_ordinary (i : I) (x : Matrix N N A) :
    Matrix.trace ((ordinary D hc).d i x) = D i (Matrix.trace x) := by
  change (∑ a, D i (x a a)) = D i (∑ a, x a a)
  exact (map_sum _ _ _).symm

variable (C : I → Matrix N N A)

theorem trace_covariant (i : I) (x : Matrix N N A) :
    Matrix.trace (covariant (ordinary D hc) C i x) = D i (Matrix.trace x) := by
  simp only [covariant_apply, Matrix.trace_add, trace_ordinary, trace_bracket, add_zero]

theorem trace_ibp (i : I) (x y : Matrix N N A) :
    Matrix.trace (covariant (ordinary D hc) C i x * y) +
      Matrix.trace (x * covariant (ordinary D hc) C i y) = D i (Matrix.trace (x * y)) := by
  rw [← Matrix.trace_add, ← covariant_mul, trace_covariant]

omit [Algebra ℂ A] in
theorem trace_conjugate (u : (Matrix N N A)ˣ) (x : Matrix N N A) :
    Matrix.trace ((u : Matrix N N A) * x * (↑u⁻¹ : Matrix N N A)) = Matrix.trace x := by
  rw [Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

theorem trace_ibp_integrated (R : Set A) (i : I) (x y : Matrix N N A) :
    DifferentialEquation.integrated D R (Matrix.trace (covariant (ordinary D hc) C i x * y)) =
      -DifferentialEquation.integrated D R (Matrix.trace (x * covariant (ordinary D hc) C i y)) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← map_add, trace_ibp]
  exact DifferentialEquation.integrated_derivative D R i _

end
end Math.MatrixTraceIBP
