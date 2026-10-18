import Physics.StandardModel.Operators.SMQCoreBranching
import Math.RepresentationTheory.SU3DoubleSpinCubeResolved

/-! Fully labelled Q/conjugate-Q cubic and complementary branches.
All six actual color/weak/spin summands are resolved, retaining the distinct
left and right spin projections. No rank or multiplicity numeral is used. -/
namespace GUT.SMQResolvedCubeBranching
set_option autoImplicit false
noncomputable section
open Math Representation SMColoredCoreBranching SMQCoreBranching
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((Module.Dual ℂ SU3DoubleSpinSquare.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

def positiveCube : Representation.Equiv ((core 0).exteriorPower 3)
    (SU3DoubleSpinCubeResolved.positiveBranches.comp (projection false)) where
  toLinearEquiv := (positiveEquiv.exteriorPower 3).toLinearEquiv.trans
    SU3DoubleSpinCubeResolved.positive.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (positiveEquiv.exteriorPower 3).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCubeResolved.positive.isIntertwining _ _ (projection false g)
      ((positiveEquiv.exteriorPower 3) x)
    exact (congrArg SU3DoubleSpinCubeResolved.positive h1).trans h2

def negativeCube : Representation.Equiv ((core 5).exteriorPower 3)
    (SU3DoubleSpinCubeResolved.negativeBranches.comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 3).toLinearEquiv.trans
    SU3DoubleSpinCubeResolved.negative.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 3).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCubeResolved.negative.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 3) x)
    exact (congrArg SU3DoubleSpinCubeResolved.negative h1).trans h2

def positiveNine : Representation.Equiv ((core 0).exteriorPower 9)
    (SU3DoubleSpinCubeResolved.positiveBranches.dual.comp (projection false)) where
  toLinearEquiv := (positiveEquiv.exteriorPower 9).toLinearEquiv.trans
    SU3DoubleSpinCubeResolved.positiveNine.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (positiveEquiv.exteriorPower 9).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCubeResolved.positiveNine.isIntertwining _ _ (projection false g)
      ((positiveEquiv.exteriorPower 9) x)
    exact (congrArg SU3DoubleSpinCubeResolved.positiveNine h1).trans h2

def negativeNine : Representation.Equiv ((core 5).exteriorPower 9)
    (SU3DoubleSpinCubeResolved.negativeBranches.dual.comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 9).toLinearEquiv.trans
    SU3DoubleSpinCubeResolved.negativeNine.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 9).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCubeResolved.negativeNine.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 9) x)
    exact (congrArg SU3DoubleSpinCubeResolved.negativeNine h1).trans h2

end
end GUT.SMQResolvedCubeBranching
