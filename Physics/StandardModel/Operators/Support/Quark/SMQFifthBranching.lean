import Physics.StandardModel.Operators.Support.Quark.SMQCoreBranching
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinFifth

/-! Actual Q-core fifth and complementary seventh color/weak/spin
decompositions. No numerical rank or multiplicity is evaluated. -/
namespace Physics.SMQFifthBranching
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

def positiveFifth : Representation.Equiv ((core 0).exteriorPower 5)
    (SU3DoubleSpinFifth.positiveBranches.comp (projection false)) :=
  (positiveEquiv.exteriorPower 5).trans
    (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinFifth.positive (projection false))

def positiveSeventh : Representation.Equiv ((core 0).exteriorPower 7)
    (SU3DoubleSpinFifth.positiveBranches.dual.comp (projection false)) :=
  (positiveEquiv.exteriorPower 7).trans
    (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinFifth.positiveSeven (projection false))

def negativeFifth : Representation.Equiv ((core 5).exteriorPower 5)
    (SU3DoubleSpinFifth.positiveBranches.dual.comp (projection true)) :=
  (negativeEquiv.exteriorPower 5).trans
    (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinFifth.negative (projection true))

def negativeSeventh : Representation.Equiv ((core 5).exteriorPower 7)
    (SU3DoubleSpinFifth.positiveBranches.comp (projection true)) :=
  (negativeEquiv.exteriorPower 7).trans
    (SplitRepresentationProjection.restrictEquiv SU3DoubleSpinFifth.negativeSeven (projection true))

end
end Physics.SMQFifthBranching
