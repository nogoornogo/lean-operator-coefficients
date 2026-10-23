import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinCubicPresentation

/-! Complete positive quartic Q-core presentation, retaining every resolved
color/weak kernel summand and its independent spin label. -/
namespace Math.SU3DoubleSpinQuarticPresentation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection JointSourcePresentation SU3DoubleSpinSquare
open SU3DoubleSpinJointAtoms
open scoped TensorProduct

@[reducible] local instance (X Y : Type*) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] : AddCommGroup (X ⊗[ℂ] Y) := inferInstance
@[reducible] local instance : AddCommGroup (Color ⊗[ℂ] Doublet) := inferInstance
@[reducible] local instance : AddCommGroup ((Color ⊗[ℂ] Doublet) ⊗[ℂ] Doublet) := inferInstance

abbrev A4 := ColorWeakQuartic.a color weakProjection
abbrev B2 := ColorWeakQuartic.b color weakProjection
abbrev C2 := ColorWeakQuartic.c color weakProjection
abbrev D2 := ColorWeakQuartic.d color weakProjection
abbrev E4 := ColorWeakQuartic.e color weakProjection
abbrev H := ColorWeakQuartic.harmonic color
abbrev K211 := ColorWeakQuartic.k211Branches color weakProjection
abbrev K22 := ColorWeakQuartic.k22Branches color weakProjection
abbrev Fourth := ColorWeakQuartic.fourthBranches color weakProjection

def a (right : Bool) : Presentation (A4.comp (projection right)) :=
  tensorComp color (SU3DoubleSpinSquare.weak.symmetricPower 4) (projection right)
    (defining right) (SU3DoubleSpinJointAtoms.weak right 4)
def b (right : Bool) : Presentation (B2.comp (projection right)) :=
  tensorComp color (SU3DoubleSpinSquare.weak.symmetricPower 2) (projection right)
    (defining right) (SU3DoubleSpinJointAtoms.weak right 2)
def c (right : Bool) : Presentation (C2.comp (projection right)) :=
  tensorComp H (SU3DoubleSpinSquare.weak.symmetricPower 2) (projection right)
    (square right) (SU3DoubleSpinJointAtoms.weak right 2)
def d (right : Bool) : Presentation (D2.comp (projection right)) :=
  tensorComp (color.dual.symmetricPower 2) (SU3DoubleSpinSquare.weak.symmetricPower 2) (projection right)
    (oppositeSymmetric right 2) (SU3DoubleSpinJointAtoms.weak right 2)
def e (right : Bool) : Presentation (E4.comp (projection right)) :=
  tensorComp (color.dual.symmetricPower 2) (SU3DoubleSpinSquare.weak.symmetricPower 4) (projection right)
    (oppositeSymmetric right 2) (SU3DoubleSpinJointAtoms.weak right 4)

def fourth (right : Bool) : Presentation (Fourth.comp (projection right)) :=
  sumComp B2 (color.dual.symmetricPower 2) (projection right) (b right) (oppositeSymmetric right 2)

def k211 (right : Bool) : Presentation (K211.comp (projection right)) :=
  sumComp A4 ((C2.prod H).prod (D2.prod (B2.prod color))) (projection right) (a right)
    (sumComp (C2.prod H) (D2.prod (B2.prod color)) (projection right)
      (sumComp C2 H (projection right) (c right) (square right))
      (sumComp D2 (B2.prod color) (projection right) (d right)
        (sumComp B2 color (projection right) (b right) (defining right))))

def k22 (right : Bool) : Presentation (K22.comp (projection right)) :=
  sumComp (E4.prod (color.dual.symmetricPower 2)) ((B2.prod C2).prod (color.symmetricPower 4))
    (projection right)
    (sumComp E4 (color.dual.symmetricPower 2) (projection right) (e right) (oppositeSymmetric right 2))
    (sumComp (B2.prod C2) (color.symmetricPower 4) (projection right)
      (sumComp B2 C2 (projection right) (b right) (c right)) (symmetric right 4))

def branches (right : Bool) : Presentation (SU3DoubleSpinQuartic.positiveBranches.comp (projection right)) :=
  sumComp (Fourth.tprod (SU3DoubleSpinSquare.spin.symmetricPower 4))
    ((K211.tprod (SU3DoubleSpinSquare.spin.symmetricPower 2)).prod K22) (projection right)
    (tensorComp Fourth (SU3DoubleSpinSquare.spin.symmetricPower 4) (projection right)
      (fourth right) (SU3DoubleSpinJointAtoms.spin right 4))
    (sumComp (K211.tprod (SU3DoubleSpinSquare.spin.symmetricPower 2)) K22 (projection right)
      (tensorComp K211 (SU3DoubleSpinSquare.spin.symmetricPower 2) (projection right)
        (k211 right) (SU3DoubleSpinJointAtoms.spin right 2)) (k22 right))

def positiveFour (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 4).comp (projection right)) :=
  alongEquiv (restrictEquiv SU3DoubleSpinQuartic.positive (projection right)) (branches right)

def positiveEight (right : Bool) : Presentation ((SU3DoubleSpinSquare.tensor.exteriorPower 8).comp (projection right)) :=
  alongEquiv (restrictEquiv (SU3DoubleSpinExterior.complement (by rfl : 8+4=12)) (projection right))
    (dualComp (SU3DoubleSpinSquare.tensor.exteriorPower 4) (projection right) (positiveFour right))

end
end Math.SU3DoubleSpinQuarticPresentation
