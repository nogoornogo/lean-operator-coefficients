import Math.Algebra.Jets.DifferentialEquationIdeal
import Math.RepresentationTheory.Jets.JetEquationIBP

/-! Exact recovery of the retained scalar linear ideal from its full linear
relation source, without assuming a nonlinear quotient is freely generated. -/
namespace Math.DifferentialEquation
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra

theorem scalar_linear_recovery {S I : Type*} (q : JetDirections.Symbols I) :
    ideal (totalDerivative (S := S))
      (Set.range (fun v : JetEquation.relations S q => JetLinear.linearForm v.val)) =
      JetEquation.ideal S q := by
  apply le_antisymm
  · apply minimal
    · exact Ideal.subset_span
    · intro i p hp
      exact JetEquation.ideal_derivative_stable q i hp
  · apply Ideal.span_le.mpr
    exact fun _ hp => seed_mem _ _ hp

end
end Math.DifferentialEquation
