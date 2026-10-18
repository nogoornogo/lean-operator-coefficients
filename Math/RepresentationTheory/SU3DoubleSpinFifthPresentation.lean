import Math.RepresentationTheory.ColorWeakJointAtoms
import Math.RepresentationTheory.SU3DoubleSpinQuarticPresentation

/-! Actual fifth and complementary seventh Q-core presentations. Every
retained color/weak branch stays joint with its independent spin label. -/
namespace Math.SU3DoubleSpinFifthPresentation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection JointSourcePresentation ExternalInvariantTensor
open ColorWeakJointAtoms
open scoped TensorProduct
@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance
@[reducible] local instance : AddCommGroup (SU3DoubleSpinSquare.Color ⊗[ℂ] SU3DoubleSpinSquare.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((SU3DoubleSpinSquare.Color ⊗[ℂ] SU3DoubleSpinSquare.Doublet) ⊗[ℂ] SU3DoubleSpinSquare.Doublet) := inferInstance

def a (n : ℕ) : Presentation ((ColorWeakFifthSlices.a n).comp retainedProjection) :=
  withWeak n (ColorWeakMiddleGauge.color.symmetricPower 2) (symmetric 2)
def d (n : ℕ) : Presentation ((ColorWeakFifthSlices.d n).comp retainedProjection) :=
  withWeak n ColorWeakMiddleGauge.color.dual oppositeDefining
def h (n : ℕ) : Presentation ((ColorWeakFifthSlices.h n).comp retainedProjection) :=
  withWeak n ColorWeakMiddleGauge.dualHarmonic oppositeSquare
def aOne : Presentation (ColorWeakFifthSlices.a1.comp retainedProjection) :=
  withWeakOne (ColorWeakMiddleGauge.color.symmetricPower 2) (symmetric 2)
def dOne : Presentation (ColorWeakFifthSlices.d1.comp retainedProjection) :=
  withWeakOne ColorWeakMiddleGauge.color.dual oppositeDefining
def hOne : Presentation (ColorWeakFifthSlices.h1.comp retainedProjection) :=
  withWeakOne ColorWeakMiddleGauge.dualHarmonic oppositeSquare
def pOne : Presentation (ColorWeakFifthSlices.p1.comp retainedProjection) :=
  withWeakOne ColorWeakMiddleGauge.cubicKernel cube

def one : Presentation (ColorWeakFifthSlices.one.comp retainedProjection) :=
  (sumComp (ColorWeakFifthSlices.d 5) ((ColorWeakFifthSlices.d 3).prod (ColorWeakFifthSlices.d1.prod ((ColorWeakFifthSlices.a 3).prod (ColorWeakFifthSlices.a1.prod ((ColorWeakFifthSlices.h 3).prod (ColorWeakFifthSlices.h1.prod ColorWeakFifthSlices.p1)))))) retainedProjection (d 5) (sumComp (ColorWeakFifthSlices.d 3) (ColorWeakFifthSlices.d1.prod ((ColorWeakFifthSlices.a 3).prod (ColorWeakFifthSlices.a1.prod ((ColorWeakFifthSlices.h 3).prod (ColorWeakFifthSlices.h1.prod ColorWeakFifthSlices.p1))))) retainedProjection (d 3) (sumComp ColorWeakFifthSlices.d1 ((ColorWeakFifthSlices.a 3).prod (ColorWeakFifthSlices.a1.prod ((ColorWeakFifthSlices.h 3).prod (ColorWeakFifthSlices.h1.prod ColorWeakFifthSlices.p1)))) retainedProjection dOne (sumComp (ColorWeakFifthSlices.a 3) (ColorWeakFifthSlices.a1.prod ((ColorWeakFifthSlices.h 3).prod (ColorWeakFifthSlices.h1.prod ColorWeakFifthSlices.p1))) retainedProjection (a 3) (sumComp ColorWeakFifthSlices.a1 ((ColorWeakFifthSlices.h 3).prod (ColorWeakFifthSlices.h1.prod ColorWeakFifthSlices.p1)) retainedProjection aOne (sumComp (ColorWeakFifthSlices.h 3) (ColorWeakFifthSlices.h1.prod ColorWeakFifthSlices.p1) retainedProjection (h 3) (sumComp ColorWeakFifthSlices.h1 ColorWeakFifthSlices.p1 retainedProjection hOne pOne)))))))

def three : Presentation (ColorWeakFifthSlices.three.comp retainedProjection) :=
  (sumComp (ColorWeakFifthSlices.a 3) ((ColorWeakFifthSlices.d 3).prod (ColorWeakFifthSlices.a1.prod (ColorWeakFifthSlices.d1.prod ColorWeakFifthSlices.h1))) retainedProjection (a 3) (sumComp (ColorWeakFifthSlices.d 3) (ColorWeakFifthSlices.a1.prod (ColorWeakFifthSlices.d1.prod ColorWeakFifthSlices.h1)) retainedProjection (d 3) (sumComp ColorWeakFifthSlices.a1 (ColorWeakFifthSlices.d1.prod ColorWeakFifthSlices.h1) retainedProjection aOne (sumComp ColorWeakFifthSlices.d1 ColorWeakFifthSlices.h1 retainedProjection dOne hOne))))

def five : Presentation (ColorWeakFifthSlices.five.comp retainedProjection) :=
  dOne

def branches (right : Bool) : Presentation (SU3DoubleSpinFifth.positiveBranches.comp (SU3DoubleSpinJointAtoms.projection right)) :=
  sumComp (external (WeakDoubletScalars.doublet.symmetricPower 1) ColorWeakFifthSlices.one)
    ((external (WeakDoubletScalars.doublet.symmetricPower 3) ColorWeakFifthSlices.three).prod
      (external (WeakDoubletScalars.doublet.symmetricPower 5) ColorWeakFifthSlices.five)) (fullProjection right)
    (externalLift right 1 ColorWeakFifthSlices.one one)
    (sumComp (external (WeakDoubletScalars.doublet.symmetricPower 3) ColorWeakFifthSlices.three)
      (external (WeakDoubletScalars.doublet.symmetricPower 5) ColorWeakFifthSlices.five) (fullProjection right)
        (externalLift right 3 ColorWeakFifthSlices.three three)
        (externalLift right 5 ColorWeakFifthSlices.five five))

def positiveFive (right : Bool) : Presentation
    ((SU3DoubleSpinSquare.tensor.exteriorPower 5).comp (SU3DoubleSpinJointAtoms.projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinFifth.positive (SU3DoubleSpinJointAtoms.projection right)) (branches right)

def positiveSeven (right : Bool) : Presentation
    ((SU3DoubleSpinSquare.tensor.exteriorPower 7).comp (SU3DoubleSpinJointAtoms.projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.complement (by rfl : 7+5=12)) (SU3DoubleSpinJointAtoms.projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower 5) (SU3DoubleSpinJointAtoms.projection right) (positiveFive right))

end
end Math.SU3DoubleSpinFifthPresentation
