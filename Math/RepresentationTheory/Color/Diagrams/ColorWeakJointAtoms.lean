import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinJointAtoms
import Math.RepresentationTheory.Color.SU3.SU3DoubleSpinFifth

/-! Retained color/weak factors of the fifth and sixth Q-core decompositions,
placed jointly with the independent left or right spin. -/
namespace Math.ColorWeakJointAtoms
set_option autoImplicit false
noncomputable section
open Representation JointSourcePresentation SplitRepresentationProjection ExternalInvariantTensor

def retainedProjection : JointColorSpinWord.Group →* ColorWeakMiddleGauge.Group where
  toFun g := (g.1,g.2.1)
  map_one' := rfl
  map_mul' _ _ := rfl

def fullProjection (right : Bool) : JointColorSpinWord.Group →*
    (TauCeti.SU2 × ColorWeakMiddleGauge.Group) :=
  SU3DoubleSpinFifth.reorder.comp (SU3DoubleSpinJointAtoms.projection right)

def defining : Presentation (ColorWeakMiddleGauge.color.comp retainedProjection) :=
  JointSourceColorPresentation.defining (ColorWeakMiddleGauge.colorProjection.comp retainedProjection) (fun _ => rfl)
def oppositeDefining : Presentation (ColorWeakMiddleGauge.color.dual.comp retainedProjection) :=
  JointSourceColorPresentation.oppositeDefining (ColorWeakMiddleGauge.colorProjection.comp retainedProjection) (fun _ => rfl)
def symmetric (n : ℕ) : Presentation ((ColorWeakMiddleGauge.color.symmetricPower n).comp retainedProjection) :=
  JointSourceColorPresentation.symmetric ColorWeakMiddleGauge.colorProjection retainedProjection (fun _ => rfl) n
def oppositeSymmetric (n : ℕ) : Presentation ((ColorWeakMiddleGauge.color.dual.symmetricPower n).comp retainedProjection) :=
  JointSourceColorPresentation.oppositeSymmetric ColorWeakMiddleGauge.colorProjection retainedProjection (fun _ => rfl) n
def weak (n : ℕ) : Presentation ((ColorWeakMiddleGauge.spin n).comp retainedProjection) :=
  JointSourceSpinPresentation.pulledWeak n ColorWeakMiddleGauge.weakProjection retainedProjection (fun _ => rfl)
def weakOne : Presentation (ColorWeakMiddleGauge.weak.comp retainedProjection) :=
  JointSourceSpinPresentation.weakDoublet (ColorWeakMiddleGauge.weakProjection.comp retainedProjection) (fun _ => rfl)
def adjoint : Presentation (ColorWeakMiddleGauge.adjoint.comp retainedProjection) :=
  JointSourceColorPresentation.adjoint ColorWeakMiddleGauge.colorProjection retainedProjection (fun _ => rfl)
def oppositeSquare : Presentation (ColorWeakMiddleGauge.dualHarmonic.comp retainedProjection) :=
  JointSourceColorPresentation.oppositeSquare ColorWeakMiddleGauge.colorProjection retainedProjection (fun _ => rfl)
def cube : Presentation (ColorWeakMiddleGauge.cubicKernel.comp retainedProjection) :=
  JointSourceColorPresentation.cube ColorWeakMiddleGauge.colorProjection retainedProjection (fun _ => rfl)
def squareSquare : Presentation (ColorWeakMiddleGauge.balancedKernel.comp retainedProjection) :=
  JointSourceColorPresentation.squareSquare ColorWeakMiddleGauge.colorProjection retainedProjection (fun _ => rfl)
def scalar : Presentation (ColorWeakMiddleGauge.scalar.comp retainedProjection) :=
  JointSourceSpinPresentation.scalarComp retainedProjection

section Generic
variable {A : Type*} [AddCommMonoid A] [Module ℂ A]

def withWeak (n : ℕ) (r : Representation ℂ ColorWeakMiddleGauge.Group A)
    (P : Presentation (r.comp retainedProjection)) :
    Presentation ((r.tprod (ColorWeakMiddleGauge.spin n)).comp retainedProjection) :=
  tensorComp r (ColorWeakMiddleGauge.spin n) retainedProjection P (weak n)

def withWeakOne (r : Representation ℂ ColorWeakMiddleGauge.Group A)
    (P : Presentation (r.comp retainedProjection)) :
    Presentation ((r.tprod ColorWeakMiddleGauge.weak).comp retainedProjection) :=
  tensorComp r ColorWeakMiddleGauge.weak retainedProjection P weakOne

def externalLift (right : Bool) (n : ℕ) (r : Representation ℂ ColorWeakMiddleGauge.Group A)
    (P : Presentation (r.comp retainedProjection)) :
    Presentation ((external (WeakDoubletScalars.doublet.symmetricPower n) r).comp (fullProjection right)) := by
  refine externalComp (WeakDoubletScalars.doublet.symmetricPower n) r (fullProjection right) ?_ ?_
  · cases right
    · exact JointSourceSpinPresentation.atLeft n
        ((MonoidHom.fst TauCeti.SU2 ColorWeakMiddleGauge.Group).comp (fullProjection false)) (fun _ => rfl)
    · exact JointSourceSpinPresentation.atRight n
        ((MonoidHom.fst TauCeti.SU2 ColorWeakMiddleGauge.Group).comp (fullProjection true)) (fun _ => rfl)
  · exact P

end Generic
end
end Math.ColorWeakJointAtoms
