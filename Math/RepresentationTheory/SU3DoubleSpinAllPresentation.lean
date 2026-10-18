import Math.RepresentationTheory.SU3DoubleSpinSixthPresentation

/-! Every Q/conjugate-Q core exterior degree has an actual joint expression.
Degrees beyond capacity are represented by the proved zero source. -/
namespace Math.SU3DoubleSpinAllPresentation
set_option autoImplicit false
noncomputable section
open Representation JointSourcePresentation SplitRepresentationProjection
open SU3DoubleSpinSquare SU3DoubleSpinJointAtoms
open scoped TensorProduct

@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

def positive (right : Bool) : (n : ℕ) →
    Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower n).comp (projection right))
  | 0 => SU3DoubleSpinLowerPresentation.positiveZero right
  | 1 => SU3DoubleSpinLowerPresentation.positiveOne right
  | 2 => SU3DoubleSpinLowerPresentation.positiveTwo right
  | 3 => SU3DoubleSpinCubicPresentation.positiveThree right
  | 4 => SU3DoubleSpinQuarticPresentation.positiveFour right
  | 5 => SU3DoubleSpinFifthPresentation.positiveFive right
  | 6 => SU3DoubleSpinSixthPresentation.positiveSix right
  | 7 => SU3DoubleSpinFifthPresentation.positiveSeven right
  | 8 => SU3DoubleSpinQuarticPresentation.positiveEight right
  | 9 => SU3DoubleSpinCubicPresentation.positiveNine right
  | 10 => SU3DoubleSpinLowerPresentation.positiveTen right
  | 11 => SU3DoubleSpinLowerPresentation.positiveEleven right
  | 12 => SU3DoubleSpinLowerPresentation.positiveTwelve right
  | n+13 => zero _ (fun x => exteriorPower.eq_zero_of_finrank_lt (n+13)
      (by rw [SU3DoubleSpinExterior.tensor_dimension]; omega) x)

def negative (right : Bool) (n : ℕ) :
    Presentation ((dualTensor.exteriorPower n).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinDuality.exterior n) (projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower n) (projection right) (positive right n))

theorem positive_allowed_iff (right : Bool) (n : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SU3DoubleSpinSquare.tensor.exteriorPower n).comp (projection right))) ↔
      JointSourceExpression.Supports (positive right n).expression :=
  JointSourcePresentation.allowed_iff (positive right n)

theorem negative_allowed_iff (right : Bool) (n : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((dualTensor.exteriorPower n).comp (projection right))) ↔
      JointSourceExpression.Supports (negative right n).expression :=
  JointSourcePresentation.allowed_iff (negative right n)

end
end Math.SU3DoubleSpinAllPresentation
