import Physics.StandardModel.Operators.SMQCoreBranching
import Math.RepresentationTheory.SU3DoubleSpinCube

/-! Actual Q/conjugate-Q cubic and complementary coarse branches.
All color, weak and left/right spin actions are retained. The color/weak
hook is not asserted to be an irreducible or completely labelled branch. -/
namespace GUT.SMQCubeBranching
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
    (SU3DoubleSpinCube.branches.comp (projection false)) where
  toLinearEquiv := (positiveEquiv.exteriorPower 3).toLinearEquiv.trans
    SU3DoubleSpinCube.positive.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (positiveEquiv.exteriorPower 3).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCube.positive.isIntertwining _ _ (projection false g)
      ((positiveEquiv.exteriorPower 3) x)
    exact (congrArg SU3DoubleSpinCube.positive h1).trans h2

def negativeCube : Representation.Equiv ((core 5).exteriorPower 3)
    (SU3DoubleSpinCube.dualBranches.comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 3).toLinearEquiv.trans
    SU3DoubleSpinCube.negative.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 3).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCube.negative.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 3) x)
    exact (congrArg SU3DoubleSpinCube.negative h1).trans h2

def positiveNine : Representation.Equiv ((core 0).exteriorPower 9)
    (SU3DoubleSpinCube.branches.dual.comp (projection false)) where
  toLinearEquiv := (positiveEquiv.exteriorPower 9).toLinearEquiv.trans
    SU3DoubleSpinCube.positiveNine.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (positiveEquiv.exteriorPower 9).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCube.positiveNine.isIntertwining _ _ (projection false g)
      ((positiveEquiv.exteriorPower 9) x)
    exact (congrArg SU3DoubleSpinCube.positiveNine h1).trans h2

def negativeNine : Representation.Equiv ((core 5).exteriorPower 9)
    (SU3DoubleSpinCube.dualBranches.dual.comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 9).toLinearEquiv.trans
    SU3DoubleSpinCube.negativeNine.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 9).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinCube.negativeNine.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 9) x)
    exact (congrArg SU3DoubleSpinCube.negativeNine h1).trans h2

end
end GUT.SMQCubeBranching
