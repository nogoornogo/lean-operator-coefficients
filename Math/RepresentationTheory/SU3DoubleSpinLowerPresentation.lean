import Math.RepresentationTheory.SU3DoubleSpinJointAtoms
import Math.RepresentationTheory.SU3DoubleSpinCubeResolved
import Math.RepresentationTheory.SU3DoubleSpinQuartic

/-! Actual zero/one/two Q-core source presentations and complementary
degrees, with complete joint branch choices rather than occurrence inputs. -/
namespace Math.SU3DoubleSpinLowerPresentation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection JointSourcePresentation SU3DoubleSpinSquare
open SU3DoubleSpinJointAtoms
open scoped TensorProduct

@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup (Module.Dual ℂ Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Module.Dual ℂ Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

section Generic
variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def first (right : Bool) (d : Representation ℂ SU3DoubleSpinSquare.Group A)
    (P : Presentation (d.comp (projection right))) :
    Presentation ((SU3DoubleSpinSquare.first d).comp (projection right)) :=
  sumComp (d.tprod ((SU3DoubleSpinSquare.weak.symmetricPower 2).tprod
      (SU3DoubleSpinSquare.spin.symmetricPower 2))) d (projection right)
    (tensorComp d ((SU3DoubleSpinSquare.weak.symmetricPower 2).tprod
        (SU3DoubleSpinSquare.spin.symmetricPower 2)) (projection right) P
      (tensorComp (SU3DoubleSpinSquare.weak.symmetricPower 2)
        (SU3DoubleSpinSquare.spin.symmetricPower 2) (projection right)
          (SU3DoubleSpinJointAtoms.weak right 2) (SU3DoubleSpinJointAtoms.spin right 2))) P

def second (right : Bool) (a : Representation ℂ SU3DoubleSpinSquare.Group A)
    (P : Presentation ((a.symmetricPower 2).comp (projection right))) :
    Presentation ((SU3DoubleSpinSquare.second a).comp (projection right)) :=
  sumComp ((a.symmetricPower 2).tprod (SU3DoubleSpinSquare.spin.symmetricPower 2))
    ((a.symmetricPower 2).tprod (SU3DoubleSpinSquare.weak.symmetricPower 2)) (projection right)
      (tensorComp (a.symmetricPower 2) (SU3DoubleSpinSquare.spin.symmetricPower 2)
        (projection right) P (SU3DoubleSpinJointAtoms.spin right 2))
      (tensorComp (a.symmetricPower 2) (SU3DoubleSpinSquare.weak.symmetricPower 2)
        (projection right) P (SU3DoubleSpinJointAtoms.weak right 2))

end Generic

def positiveTwoBranches (right : Bool) : Presentation
    (((SU3DoubleSpinSquare.first color.dual).prod (SU3DoubleSpinSquare.second color)).comp (projection right)) :=
  sumComp (SU3DoubleSpinSquare.first color.dual) (SU3DoubleSpinSquare.second color) (projection right)
    (first right color.dual (oppositeDefining right))
    (second right color (symmetric right 2))

def negativeTwoBranches (right : Bool) : Presentation
    (((SU3DoubleSpinSquare.first color).prod (SU3DoubleSpinSquare.second color.dual)).comp (projection right)) :=
  sumComp (SU3DoubleSpinSquare.first color) (SU3DoubleSpinSquare.second color.dual) (projection right)
    (first right color (defining right))
    (second right color.dual (oppositeSymmetric right 2))

def positiveZero (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 0).comp (projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinSquare.tensor.exteriorPowerZeroEquiv (projection right)) (SU3DoubleSpinJointAtoms.scalar right)
def negativeZero (right : Bool) : Presentation ((dualTensor.exteriorPower 0).comp (projection right)) :=
  alongEquiv (restrictEquiv dualTensor.exteriorPowerZeroEquiv (projection right)) (SU3DoubleSpinJointAtoms.scalar right)
def positiveOne (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 1).comp (projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinSquare.tensor.exteriorPowerOneEquiv (projection right)) (SU3DoubleSpinJointAtoms.positiveOne right)
def negativeOne (right : Bool) : Presentation ((dualTensor.exteriorPower 1).comp (projection right)) :=
  alongEquiv (restrictEquiv dualTensor.exteriorPowerOneEquiv (projection right)) (SU3DoubleSpinJointAtoms.negativeOne right)
def positiveTwo (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 2).comp (projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinSquare.positive (projection right)) (positiveTwoBranches right)
def negativeTwo (right : Bool) : Presentation ((dualTensor.exteriorPower 2).comp (projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinSquare.negative (projection right)) (negativeTwoBranches right)

def positiveTwelve (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 12).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.complement (by rfl : 12+0=12)) (projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower 0) (projection right) (positiveZero right))
def negativeTwelve (right : Bool) : Presentation ((dualTensor.exteriorPower 12).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.dualComplement (by rfl : 12+0=12)) (projection right))
    (dualComp (dualTensor.exteriorPower 0) (projection right) (negativeZero right))
def positiveEleven (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 11).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.complement (by rfl : 11+1=12)) (projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower 1) (projection right) (positiveOne right))
def negativeEleven (right : Bool) : Presentation ((dualTensor.exteriorPower 11).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.dualComplement (by rfl : 11+1=12)) (projection right))
    (dualComp (dualTensor.exteriorPower 1) (projection right) (negativeOne right))
def positiveTen (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 10).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.complement (by rfl : 10+2=12)) (projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower 2) (projection right) (positiveTwo right))
def negativeTen (right : Bool) : Presentation ((dualTensor.exteriorPower 10).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.dualComplement (by rfl : 10+2=12)) (projection right))
    (dualComp (dualTensor.exteriorPower 2) (projection right) (negativeTwo right))

end
end Math.SU3DoubleSpinLowerPresentation
