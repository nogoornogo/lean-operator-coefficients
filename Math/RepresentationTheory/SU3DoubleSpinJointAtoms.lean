import Math.RepresentationTheory.SU3DoubleSpinSquare
import Math.RepresentationTheory.JointSourceColorPresentation
import Math.RepresentationTheory.JointSourceSpinPresentation

/-! Actual color and independent weak/spin atoms for every retained Q-core
branch, placed in the common color/weak/left/right source group. -/
namespace Math.SU3DoubleSpinJointAtoms
set_option autoImplicit false
noncomputable section
open Representation JointSourcePresentation SU3DoubleSpinSquare

def projection (right : Bool) : JointColorSpinWord.Group →* SU3DoubleSpinSquare.Group where
  toFun g := (g.1,(g.2.1,if right then g.2.2.2 else g.2.2.1))
  map_one' := by cases right <;> rfl
  map_mul' _ _ := by cases right <;> rfl

def defining (right : Bool) : Presentation (color.comp (projection right)) :=
  JointSourceColorPresentation.defining ((MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)).comp (projection right)) (fun _ => rfl)

def oppositeDefining (right : Bool) : Presentation (color.dual.comp (projection right)) :=
  JointSourceColorPresentation.oppositeDefining ((MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)).comp (projection right)) (fun _ => rfl)

def symmetric (right : Bool) (n : ℕ) : Presentation ((color.symmetricPower n).comp (projection right)) :=
  JointSourceColorPresentation.symmetric (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl) n

def oppositeSymmetric (right : Bool) (n : ℕ) :
    Presentation ((color.dual.symmetricPower n).comp (projection right)) :=
  JointSourceColorPresentation.oppositeSymmetric (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl) n

def weak (right : Bool) (n : ℕ) :
    Presentation ((SU3DoubleSpinSquare.weak.symmetricPower n).comp (projection right)) :=
  JointSourceSpinPresentation.pulledWeak n weakProjection (projection right) (fun _ => rfl)

def spin (right : Bool) (n : ℕ) :
    Presentation ((SU3DoubleSpinSquare.spin.symmetricPower n).comp (projection right)) := by
  cases right
  · exact JointSourceSpinPresentation.pulledLeft n spinProjection (projection false) (fun _ => rfl)
  · exact JointSourceSpinPresentation.pulledRight n spinProjection (projection true) (fun _ => rfl)

def weakOne (right : Bool) : Presentation (SU3DoubleSpinSquare.weak.comp (projection right)) :=
  JointSourceSpinPresentation.weakDoublet (weakProjection.comp (projection right)) (fun _ => rfl)

def spinOne (right : Bool) : Presentation (SU3DoubleSpinSquare.spin.comp (projection right)) := by
  cases right
  · exact JointSourceSpinPresentation.leftDoublet (spinProjection.comp (projection false)) (fun _ => rfl)
  · exact JointSourceSpinPresentation.rightDoublet (spinProjection.comp (projection true)) (fun _ => rfl)

def adjoint (right : Bool) :
    Presentation ((TraceEndomorphismSplit.traceFreeAction color).comp (projection right)) :=
  JointSourceColorPresentation.adjoint (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl)

def oppositeAdjoint (right : Bool) :
    Presentation ((TraceEndomorphismSplit.traceFreeAction color.dual).comp (projection right)) :=
  JointSourceColorPresentation.oppositeAdjoint (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl)

def square (right : Bool) :
    Presentation ((SymmetricSquareContractionRepresentation.action color).comp (projection right)) :=
  JointSourceColorPresentation.square (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl)

def oppositeSquare (right : Bool) :
    Presentation ((SymmetricSquareContractionRepresentation.action color.dual).comp (projection right)) :=
  JointSourceColorPresentation.oppositeSquare (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl)

def cube (right : Bool) :
    Presentation ((SymmetricCubeContractionRepresentation.action color).comp (projection right)) :=
  JointSourceColorPresentation.cube (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl)

def squareSquare (right : Bool) :
    Presentation ((SymmetricSquarePartialTraceRepresentation.action color).comp (projection right)) :=
  JointSourceColorPresentation.squareSquare (MonoidHom.fst SU3DefiningExterior.Group (TauCeti.SU2 × TauCeti.SU2)) (projection right) (fun _ => rfl)

def scalar (right : Bool) : Presentation ((trivial ℂ SU3DoubleSpinSquare.Group ℂ).comp (projection right)) :=
  JointSourceSpinPresentation.scalarComp (projection right)

def positiveOne (right : Bool) : Presentation (SU3DoubleSpinSquare.tensor.comp (projection right)) :=
  tensorComp (color.tprod SU3DoubleSpinSquare.weak) SU3DoubleSpinSquare.spin (projection right)
    (tensorComp color SU3DoubleSpinSquare.weak (projection right)
      (defining right) (weakOne right)) (spinOne right)

def negativeOne (right : Bool) : Presentation (SU3DoubleSpinSquare.dualTensor.comp (projection right)) :=
  tensorComp (color.dual.tprod SU3DoubleSpinSquare.weak) SU3DoubleSpinSquare.spin (projection right)
    (tensorComp color.dual SU3DoubleSpinSquare.weak (projection right)
      (oppositeDefining right) (weakOne right)) (spinOne right)

end
end Math.SU3DoubleSpinJointAtoms
