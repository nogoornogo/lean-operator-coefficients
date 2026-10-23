import Math.RepresentationTheory.Color.SU3.SU3SpinJointPresentation
import Physics.StandardModel.Operators.Support.Quark.SMColoredCoreBranching

/-! Actual U/D and conjugate-U/D single-generation cores in the positive
joint support syntax, uniformly in the exterior degree. -/
namespace Physics.SMColoredJointPresentation
set_option autoImplicit false
noncomputable section
open Math Representation JointSourcePresentation
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

def positive (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) (n : ℕ) :
    Presentation ((SMColoredCoreBranching.core s).exteriorPower n) :=
  alongEquiv (SMColoredCoreBranching.positiveExteriorEquiv s hs n) (SU3SpinJointPresentation.positive true n)

def negative (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) (n : ℕ) :
    Presentation ((SMColoredCoreBranching.core s).exteriorPower n) :=
  alongEquiv (SMColoredCoreBranching.negativeExteriorEquiv s hs n) (SU3SpinJointPresentation.negative false n)

theorem positive_allowed_iff (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) (n : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants ((SMColoredCoreBranching.core s).exteriorPower n)) ↔
      JointSourceExpression.Supports (positive s hs n).expression :=
  JointSourcePresentation.allowed_iff (positive s hs n)

theorem negative_allowed_iff (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) (n : ℕ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants ((SMColoredCoreBranching.core s).exteriorPower n)) ↔
      JointSourceExpression.Supports (negative s hs n).expression :=
  JointSourcePresentation.allowed_iff (negative s hs n)

end
end Physics.SMColoredJointPresentation
