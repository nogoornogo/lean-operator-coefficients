import Math.RepresentationTheory.SU3DoubleSpinFifthPresentation
import Math.RepresentationTheory.SU3DoubleSpinSixth

/-! Actual complete sixth Q-core presentation, with all retained summands
and the independent weak/left/right spin coordinates. -/
namespace Math.SU3DoubleSpinSixthPresentation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection JointSourcePresentation ExternalInvariantTensor
open ColorWeakJointAtoms
open scoped TensorProduct
@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance
@[reducible] local instance : AddCommGroup (SU3DoubleSpinSquare.Color ⊗[ℂ] SU3DoubleSpinSquare.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((SU3DoubleSpinSquare.Color ⊗[ℂ] SU3DoubleSpinSquare.Doublet) ⊗[ℂ] SU3DoubleSpinSquare.Doublet) := inferInstance

def e (n : ℕ) : Presentation ((ColorWeakSixthSlices.e n).comp retainedProjection) :=
  withWeak n ColorWeakMiddleGauge.adjoint ColorWeakJointAtoms.adjoint
def c (n : ℕ) : Presentation ((ColorWeakSixthSlices.c n).comp retainedProjection) :=
  withWeak n (ColorWeakMiddleGauge.color.symmetricPower 3) (symmetric 3)
def d (n : ℕ) : Presentation ((ColorWeakSixthSlices.d n).comp retainedProjection) :=
  withWeak n (ColorWeakMiddleGauge.color.dual.symmetricPower 3) (oppositeSymmetric 3)
def h (n : ℕ) : Presentation ((ColorWeakSixthSlices.h n).comp retainedProjection) :=
  withWeak n ColorWeakMiddleGauge.balancedKernel squareSquare

def six : Presentation (ColorWeakSixthSlices.six.comp retainedProjection) :=
  ColorWeakJointAtoms.scalar

def four : Presentation (ColorWeakSixthSlices.four.comp retainedProjection) :=
  (sumComp (ColorWeakMiddleGauge.spin 2) ((ColorWeakSixthSlices.e 2).prod ColorWeakMiddleGauge.adjoint) retainedProjection (ColorWeakJointAtoms.weak 2) (sumComp (ColorWeakSixthSlices.e 2) ColorWeakMiddleGauge.adjoint retainedProjection (e 2) ColorWeakJointAtoms.adjoint))

def two : Presentation (ColorWeakSixthSlices.two.comp retainedProjection) :=
  (sumComp (ColorWeakMiddleGauge.spin 4) ((ColorWeakSixthSlices.e 4).prod ((ColorWeakSixthSlices.e 2).prod ((ColorWeakSixthSlices.e 2).prod (ColorWeakMiddleGauge.scalar.prod (ColorWeakMiddleGauge.adjoint.prod ((ColorWeakSixthSlices.c 2).prod ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel))))))) retainedProjection (ColorWeakJointAtoms.weak 4) (sumComp (ColorWeakSixthSlices.e 4) ((ColorWeakSixthSlices.e 2).prod ((ColorWeakSixthSlices.e 2).prod (ColorWeakMiddleGauge.scalar.prod (ColorWeakMiddleGauge.adjoint.prod ((ColorWeakSixthSlices.c 2).prod ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel)))))) retainedProjection (e 4) (sumComp (ColorWeakSixthSlices.e 2) ((ColorWeakSixthSlices.e 2).prod (ColorWeakMiddleGauge.scalar.prod (ColorWeakMiddleGauge.adjoint.prod ((ColorWeakSixthSlices.c 2).prod ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel))))) retainedProjection (e 2) (sumComp (ColorWeakSixthSlices.e 2) (ColorWeakMiddleGauge.scalar.prod (ColorWeakMiddleGauge.adjoint.prod ((ColorWeakSixthSlices.c 2).prod ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel)))) retainedProjection (e 2) (sumComp ColorWeakMiddleGauge.scalar (ColorWeakMiddleGauge.adjoint.prod ((ColorWeakSixthSlices.c 2).prod ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel))) retainedProjection ColorWeakJointAtoms.scalar (sumComp ColorWeakMiddleGauge.adjoint ((ColorWeakSixthSlices.c 2).prod ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel)) retainedProjection ColorWeakJointAtoms.adjoint (sumComp (ColorWeakSixthSlices.c 2) ((ColorWeakSixthSlices.d 2).prod ColorWeakMiddleGauge.balancedKernel) retainedProjection (c 2) (sumComp (ColorWeakSixthSlices.d 2) ColorWeakMiddleGauge.balancedKernel retainedProjection (d 2) squareSquare))))))))

def zero : Presentation (ColorWeakSixthSlices.zero.comp retainedProjection) :=
  (sumComp (ColorWeakMiddleGauge.spin 6) ((ColorWeakMiddleGauge.spin 2).prod ((ColorWeakSixthSlices.e 4).prod ((ColorWeakSixthSlices.e 2).prod ((ColorWeakMiddleGauge.color.symmetricPower 3).prod ((ColorWeakMiddleGauge.color.dual.symmetricPower 3).prod (ColorWeakSixthSlices.h 2)))))) retainedProjection (ColorWeakJointAtoms.weak 6) (sumComp (ColorWeakMiddleGauge.spin 2) ((ColorWeakSixthSlices.e 4).prod ((ColorWeakSixthSlices.e 2).prod ((ColorWeakMiddleGauge.color.symmetricPower 3).prod ((ColorWeakMiddleGauge.color.dual.symmetricPower 3).prod (ColorWeakSixthSlices.h 2))))) retainedProjection (ColorWeakJointAtoms.weak 2) (sumComp (ColorWeakSixthSlices.e 4) ((ColorWeakSixthSlices.e 2).prod ((ColorWeakMiddleGauge.color.symmetricPower 3).prod ((ColorWeakMiddleGauge.color.dual.symmetricPower 3).prod (ColorWeakSixthSlices.h 2)))) retainedProjection (e 4) (sumComp (ColorWeakSixthSlices.e 2) ((ColorWeakMiddleGauge.color.symmetricPower 3).prod ((ColorWeakMiddleGauge.color.dual.symmetricPower 3).prod (ColorWeakSixthSlices.h 2))) retainedProjection (e 2) (sumComp (ColorWeakMiddleGauge.color.symmetricPower 3) ((ColorWeakMiddleGauge.color.dual.symmetricPower 3).prod (ColorWeakSixthSlices.h 2)) retainedProjection (symmetric 3) (sumComp (ColorWeakMiddleGauge.color.dual.symmetricPower 3) (ColorWeakSixthSlices.h 2) retainedProjection (oppositeSymmetric 3) (h 2)))))))

def branches (right : Bool) : Presentation (SU3DoubleSpinSixth.positiveBranches.comp (SU3DoubleSpinJointAtoms.projection right)) :=
  (sumComp (external (WeakDoubletScalars.doublet.symmetricPower 0) ColorWeakSixthSlices.zero) ((external (WeakDoubletScalars.doublet.symmetricPower 2) ColorWeakSixthSlices.two).prod ((external (WeakDoubletScalars.doublet.symmetricPower 4) ColorWeakSixthSlices.four).prod (external (WeakDoubletScalars.doublet.symmetricPower 6) ColorWeakSixthSlices.six))) (fullProjection right) (externalLift right 0 ColorWeakSixthSlices.zero zero) (sumComp (external (WeakDoubletScalars.doublet.symmetricPower 2) ColorWeakSixthSlices.two) ((external (WeakDoubletScalars.doublet.symmetricPower 4) ColorWeakSixthSlices.four).prod (external (WeakDoubletScalars.doublet.symmetricPower 6) ColorWeakSixthSlices.six)) (fullProjection right) (externalLift right 2 ColorWeakSixthSlices.two two) (sumComp (external (WeakDoubletScalars.doublet.symmetricPower 4) ColorWeakSixthSlices.four) (external (WeakDoubletScalars.doublet.symmetricPower 6) ColorWeakSixthSlices.six) (fullProjection right) (externalLift right 4 ColorWeakSixthSlices.four four) (externalLift right 6 ColorWeakSixthSlices.six six))))

def positiveSix (right : Bool) : Presentation
    ((SU3DoubleSpinSquare.tensor.exteriorPower 6).comp (SU3DoubleSpinJointAtoms.projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinSixth.positive (SU3DoubleSpinJointAtoms.projection right)) (branches right)

end
end Math.SU3DoubleSpinSixthPresentation
