import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinLowerPresentation

/-! Complete positive cubic Q-core presentation in the joint source syntax.
All six branches retain their actual color, weak and spin factors. -/
namespace Math.SU3DoubleSpinCubicPresentation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection JointSourcePresentation SU3DoubleSpinSquare
open SU3DoubleSpinJointAtoms
open scoped TensorProduct

@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

def adjointWeak (right : Bool) : Presentation (SU3DoubleSpinCube.adjointWeak.comp (projection right)) :=
  tensorComp SU3DoubleSpinCubeResolved.adjoint SU3DoubleSpinSquare.weak (projection right)
    (SU3DoubleSpinJointAtoms.adjoint right) (weakOne right)

def first (right : Bool) : Presentation (SU3DoubleSpinCube.first.comp (projection right)) :=
  tensorComp (SU3DoubleSpinSquare.weak.symmetricPower 3) (SU3DoubleSpinSquare.spin.symmetricPower 3)
    (projection right) (SU3DoubleSpinJointAtoms.weak right 3) (SU3DoubleSpinJointAtoms.spin right 3)

def second (right : Bool) : Presentation (SU3DoubleSpinCube.second.comp (projection right)) :=
  tensorComp SU3DoubleSpinCube.adjointWeak (SU3DoubleSpinSquare.spin.symmetricPower 3)
    (projection right) (adjointWeak right) (SU3DoubleSpinJointAtoms.spin right 3)

section Generic
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]

def rest (right : Bool) (r : Representation ℂ SU3DoubleSpinSquare.Group A)
    (t : Representation ℂ SU3DoubleSpinSquare.Group B)
    (R : Presentation ((r.symmetricPower 3).comp (projection right)))
    (T : Presentation (t.comp (projection right))) :
    Presentation ((SU3DoubleSpinCubeResolved.spinBranches r t).comp (projection right)) :=
  sumComp
    ((SU3DoubleSpinSquare.weak.tprod SU3DoubleSpinSquare.spin).prod
      ((t.tprod (SU3DoubleSpinSquare.weak.symmetricPower 3)).tprod SU3DoubleSpinSquare.spin))
    ((((r.symmetricPower 3).tprod SU3DoubleSpinSquare.weak).tprod SU3DoubleSpinSquare.spin).prod
      ((t.tprod SU3DoubleSpinSquare.weak).tprod SU3DoubleSpinSquare.spin)) (projection right)
    (sumComp (SU3DoubleSpinSquare.weak.tprod SU3DoubleSpinSquare.spin)
      ((t.tprod (SU3DoubleSpinSquare.weak.symmetricPower 3)).tprod SU3DoubleSpinSquare.spin)
      (projection right)
      (tensorComp SU3DoubleSpinSquare.weak SU3DoubleSpinSquare.spin (projection right) (weakOne right) (spinOne right))
      (tensorComp (t.tprod (SU3DoubleSpinSquare.weak.symmetricPower 3)) SU3DoubleSpinSquare.spin
        (projection right) (tensorComp t (SU3DoubleSpinSquare.weak.symmetricPower 3) (projection right)
          T (SU3DoubleSpinJointAtoms.weak right 3)) (spinOne right)))
    (sumComp (((r.symmetricPower 3).tprod SU3DoubleSpinSquare.weak).tprod SU3DoubleSpinSquare.spin)
      ((t.tprod SU3DoubleSpinSquare.weak).tprod SU3DoubleSpinSquare.spin) (projection right)
      (tensorComp ((r.symmetricPower 3).tprod SU3DoubleSpinSquare.weak) SU3DoubleSpinSquare.spin
        (projection right) (tensorComp (r.symmetricPower 3) SU3DoubleSpinSquare.weak (projection right)
          R (weakOne right)) (spinOne right))
      (tensorComp (t.tprod SU3DoubleSpinSquare.weak) SU3DoubleSpinSquare.spin
        (projection right) (tensorComp t SU3DoubleSpinSquare.weak (projection right) T (weakOne right)) (spinOne right)))

end Generic

def branches (right : Bool) : Presentation (SU3DoubleSpinCubeResolved.positiveBranches.comp (projection right)) :=
  sumComp (SU3DoubleSpinCube.first.prod SU3DoubleSpinCube.second)
    (SU3DoubleSpinCubeResolved.spinBranches color SU3DoubleSpinCubeResolved.adjoint) (projection right)
    (sumComp SU3DoubleSpinCube.first SU3DoubleSpinCube.second (projection right) (first right) (second right))
    (rest right color SU3DoubleSpinCubeResolved.adjoint (symmetric right 3) (SU3DoubleSpinJointAtoms.adjoint right))

def positiveThree (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 3).comp (projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinCubeResolved.positive (projection right)) (branches right)

def positiveNine (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 9).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.complement (by rfl : 9+3=12)) (projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower 3) (projection right) (positiveThree right))

end
end Math.SU3DoubleSpinCubicPresentation
