import Math.RepresentationTheory.SU3DoubleSpinAllPresentation
import Physics.StandardModel.Operators.SMQCoreBranching

/-! Every actual Q/conjugate-Q single-generation exterior source has a
joint positive support presentation, including overflow and Higgs weak
constituents. Generation/species composition remains a separate consumer. -/
namespace GUT.SMQJointPresentation
set_option autoImplicit false
noncomputable section
open Math Representation JointSourcePresentation
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (Module.Dual ℂ (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((Module.Dual ℂ SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def positive (n : ℕ) : Presentation ((SMColoredCoreBranching.core 0).exteriorPower n) :=
  alongEquiv (SMQCoreBranching.positiveEquiv.exteriorPower n) (SU3DoubleSpinAllPresentation.positive false n)

def negative (n : ℕ) : Presentation ((SMColoredCoreBranching.core 5).exteriorPower n) :=
  alongEquiv (SMQCoreBranching.negativeEquiv.exteriorPower n) (SU3DoubleSpinAllPresentation.negative true n)

def weak (m : ℕ) : Presentation (SMGenerationCauchy.weak.symmetricPower m) :=
  JointSourceSpinPresentation.pulledWeak m SMGenerationCauchy.weakProjection
    (MonoidHom.id JointColorSpinWord.Group) (fun _ => rfl)

def positiveWithWeak (n m : ℕ) : Presentation
    (((SMColoredCoreBranching.core 0).exteriorPower n).tprod (SMGenerationCauchy.weak.symmetricPower m)) :=
  tensor (positive n) (weak m)

def negativeWithWeak (n m : ℕ) : Presentation
    (((SMColoredCoreBranching.core 5).exteriorPower n).tprod (SMGenerationCauchy.weak.symmetricPower m)) :=
  tensor (negative n) (weak m)

theorem positive_allowed_iff (n m : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants
      (((SMColoredCoreBranching.core 0).exteriorPower n).tprod (SMGenerationCauchy.weak.symmetricPower m))) ↔
      JointSourceExpression.Supports (positiveWithWeak n m).expression :=
  JointSourcePresentation.allowed_iff (positiveWithWeak n m)

theorem negative_allowed_iff (n m : ℕ) : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants
      (((SMColoredCoreBranching.core 5).exteriorPower n).tprod (SMGenerationCauchy.weak.symmetricPower m))) ↔
      JointSourceExpression.Supports (negativeWithWeak n m).expression :=
  JointSourcePresentation.allowed_iff (negativeWithWeak n m)

end
end GUT.SMQJointPresentation
