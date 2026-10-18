import Physics.StandardModel.Operators.SMQCoreBranching
import Math.RepresentationTheory.SU3DoubleSpinQuartic

/-! Q/conjugate-Q quartic and complementary branches with actual color/weak resolution.
All quartic kernel summands are resolved into fixed color factors and weak labels, retaining the distinct
left and right spin projections. No rank or multiplicity numeral is used. -/
namespace GUT.SMQQuarticBranching
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

def positiveFourth : Representation.Equiv ((core 0).exteriorPower 4)
    (SU3DoubleSpinQuartic.positiveBranches.comp (projection false)) where
  toLinearEquiv := (positiveEquiv.exteriorPower 4).toLinearEquiv.trans
    SU3DoubleSpinQuartic.positive.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (positiveEquiv.exteriorPower 4).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinQuartic.positive.isIntertwining _ _ (projection false g)
      ((positiveEquiv.exteriorPower 4) x)
    exact (congrArg SU3DoubleSpinQuartic.positive h1).trans h2

def negativeFourth : Representation.Equiv ((core 5).exteriorPower 4)
    (SU3DoubleSpinQuartic.negativeBranches.comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 4).toLinearEquiv.trans
    SU3DoubleSpinQuartic.negative.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 4).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinQuartic.negative.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 4) x)
    exact (congrArg SU3DoubleSpinQuartic.negative h1).trans h2

def positiveEight : Representation.Equiv ((core 0).exteriorPower 8)
    (SU3DoubleSpinQuartic.positiveBranches.dual.comp (projection false)) where
  toLinearEquiv := (positiveEquiv.exteriorPower 8).toLinearEquiv.trans
    SU3DoubleSpinQuartic.positiveEight.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (positiveEquiv.exteriorPower 8).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinQuartic.positiveEight.isIntertwining _ _ (projection false g)
      ((positiveEquiv.exteriorPower 8) x)
    exact (congrArg SU3DoubleSpinQuartic.positiveEight h1).trans h2

def negativeEight : Representation.Equiv ((core 5).exteriorPower 8)
    (SU3DoubleSpinQuartic.negativeBranches.dual.comp (projection true)) where
  toLinearEquiv := (negativeEquiv.exteriorPower 8).toLinearEquiv.trans
    SU3DoubleSpinQuartic.negativeEight.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h1 := (negativeEquiv.exteriorPower 8).isIntertwining _ _ g x
    have h2 := SU3DoubleSpinQuartic.negativeEight.isIntertwining _ _ (projection true g)
      ((negativeEquiv.exteriorPower 8) x)
    exact (congrArg SU3DoubleSpinQuartic.negativeEight h1).trans h2

end
end GUT.SMQQuarticBranching
