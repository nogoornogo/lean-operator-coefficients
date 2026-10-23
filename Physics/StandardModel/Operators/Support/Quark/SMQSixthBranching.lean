import Physics.StandardModel.Operators.Support.Quark.SMQCoreBranching
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinSixth

/-! Complete actual positive-Q sixth exterior color/weak/spin branching.
No numerical multiplicity or rank certificate is used. -/
namespace Physics.SMQSixthBranching
set_option autoImplicit false
noncomputable section
open Math Representation SMColoredCoreBranching SMQCoreBranching
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((Module.Dual ℂ SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def positiveSixth : Representation.Equiv ((core 0).exteriorPower 6)
    (SU3DoubleSpinSixth.positiveBranches.comp (projection false)) :=
  (positiveEquiv.exteriorPower 6).trans
    (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinSixth.positive (projection false))

def negativeSixth : Representation.Equiv ((core 5).exteriorPower 6)
    (SU3DoubleSpinSixth.positiveBranches.dual.comp (projection true)) :=
  (negativeEquiv.exteriorPower 6).trans
    (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinSixth.negative (projection true))

end
end Physics.SMQSixthBranching
