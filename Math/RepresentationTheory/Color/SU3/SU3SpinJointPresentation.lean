import Math.RepresentationTheory.Color.SU3.SU3SpinExteriorCube
import Math.RepresentationTheory.Color.SU3.SU3ConjugateSpinExterior
import Math.RepresentationTheory.Constructions.JointSourceColorPresentation
import Math.RepresentationTheory.Constructions.JointSourceSpinPresentation
import Math.RepresentationTheory.Exterior.ExteriorDualEquivalence

/-! Complete color/single-spin core presentations, for both independent
spin placements and actual conjugate color, at every exterior degree. -/
namespace Math.SU3SpinJointPresentation
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection JointSourcePresentation
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (SU3SpinExterior.Color ⊗[ℂ] SU3SpinExterior.Spin) := inferInstance
@[reducible] local instance : AddCommGroup (SU3ConjugateSpinExterior.Color ⊗[ℂ] SU3SpinExterior.Spin) := inferInstance

def projection (right : Bool) : JointColorSpinWord.Group →* SU3SpinExterior.Group where
  toFun g := (g.1,if right then g.2.2.2 else g.2.2.1)
  map_one' := by cases right <;> rfl
  map_mul' _ _ := by cases right <;> rfl

def spin (right : Bool) (n : ℕ) : Presentation ((SU3SpinExterior.spin.symmetricPower n).comp (projection right)) := by
  cases right
  · exact JointSourceSpinPresentation.pulledLeft n (MonoidHom.snd SU3DefiningExterior.Group TauCeti.SU2)
      (projection false) (fun _ => rfl)
  · exact JointSourceSpinPresentation.pulledRight n (MonoidHom.snd SU3DefiningExterior.Group TauCeti.SU2)
      (projection true) (fun _ => rfl)

def spinOne (right : Bool) : Presentation (SU3SpinExterior.spin.comp (projection right)) := by
  cases right
  · exact JointSourceSpinPresentation.leftDoublet
      ((MonoidHom.snd SU3DefiningExterior.Group TauCeti.SU2).comp (projection false)) (fun _ => rfl)
  · exact JointSourceSpinPresentation.rightDoublet
      ((MonoidHom.snd SU3DefiningExterior.Group TauCeti.SU2).comp (projection true)) (fun _ => rfl)

def defining (right : Bool) : Presentation (SU3SpinExterior.color.comp (projection right)) :=
  JointSourceColorPresentation.defining
    ((MonoidHom.fst SU3DefiningExterior.Group TauCeti.SU2).comp (projection right)) (fun _ => rfl)

def scalar (right : Bool) : Presentation ((trivial ℂ SU3SpinExterior.Group ℂ).comp (projection right)) :=
  JointSourceSpinPresentation.scalarComp (projection right)

def one (right : Bool) : Presentation (SU3SpinExterior.tensor.comp (projection right)) :=
  tensorComp SU3SpinExterior.color SU3SpinExterior.spin (projection right) (defining right) (spinOne right)

def first (right : Bool) : Presentation (SU3SpinExterior.firstBranch.comp (projection right)) :=
  externalComp SU3DefiningExterior.rho.dual (WeakDoubletScalars.doublet.symmetricPower 2) (projection right)
    (JointSourceColorPresentation.oppositeDefining
      ((MonoidHom.fst SU3DefiningExterior.Group TauCeti.SU2).comp (projection right)) (fun _ => rfl)) (spin right 2)

def second (right : Bool) : Presentation (SU3SpinExterior.secondBranch.comp (projection right)) :=
  JointSourceColorPresentation.symmetric (MonoidHom.fst SU3DefiningExterior.Group TauCeti.SU2)
    (projection right) (fun _ => rfl) 2

def two (right : Bool) : Presentation ((SU3SpinExterior.firstBranch.prod SU3SpinExterior.secondBranch).comp (projection right)) :=
  sumComp SU3SpinExterior.firstBranch SU3SpinExterior.secondBranch (projection right) (first right) (second right)

def middle (right : Bool) : Presentation (SU3SpinExteriorCube.middleBranch.comp (projection right)) :=
  externalComp SU3ColorPair.adjoint WeakDoubletScalars.doublet (projection right)
    (JointSourceColorPresentation.atColor .adjoint SU3ColorPair.adjoint (.refl _)
      ((MonoidHom.fst SU3DefiningExterior.Group TauCeti.SU2).comp (projection right)) (fun _ => rfl)) (spinOne right)

def three (right : Bool) : Presentation
    ((SU3SpinExteriorCube.topBranch.prod SU3SpinExteriorCube.middleBranch).comp (projection right)) :=
  sumComp SU3SpinExteriorCube.topBranch SU3SpinExteriorCube.middleBranch (projection right) (spin right 3) (middle right)

def positive (right : Bool) : (n : ℕ) → Presentation ((SU3SpinExterior.tensor.exteriorPower n).comp (projection right))
  | 0 => alongEquiv (restrictEquiv SU3SpinExterior.tensor.exteriorPowerZeroEquiv (projection right)) (scalar right)
  | 1 => alongEquiv (restrictEquiv SU3SpinExterior.tensor.exteriorPowerOneEquiv (projection right)) (one right)
  | 2 => alongEquiv (restrictEquiv SU3SpinExterior.squareEquiv (projection right)) (two right)
  | 3 => alongEquiv (restrictEquiv SU3SpinExteriorCube.cubeEquiv (projection right)) (three right)
  | 4 => alongEquiv (restrictEquiv SU3SpinExterior.fourEquiv (projection right))
      (dualComp (SU3SpinExterior.firstBranch.prod SU3SpinExterior.secondBranch) (projection right) (two right))
  | 5 => alongEquiv (restrictEquiv SU3SpinExterior.fiveEquiv (projection right))
      (dualComp SU3SpinExterior.tensor (projection right) (one right))
  | 6 => alongEquiv (restrictEquiv SU3SpinExterior.sixEquiv (projection right)) (scalar right)
  | n+7 => zero _ (SU3SpinExterior.high_zero (n+7) (by omega))

def spinSelfDual : Representation.Equiv SU3SpinExterior.spin SU3SpinExterior.spin.dual where
  toLinearEquiv := SU2DoubletDuality.equivalence.toLinearEquiv
  isIntertwining' g := SU2DoubletDuality.equivalence.isIntertwining' g.2

def conjugateEquivalence : Representation.Equiv SU3ConjugateSpinExterior.tensor SU3SpinExterior.tensor.dual :=
  (tensorEquiv (.refl SU3SpinExterior.color.dual) spinSelfDual).trans
    (InvariantTensorCurry.tensorDual SU3SpinExterior.color SU3SpinExterior.spin)

def exteriorConjugate (n : ℕ) : Representation.Equiv (SU3ConjugateSpinExterior.tensor.exteriorPower n)
    (SU3SpinExterior.tensor.exteriorPower n).dual :=
  (conjugateEquivalence.exteriorPower n).trans (ExteriorDualEquivalence.equivalence SU3SpinExterior.tensor n)

def negative (right : Bool) (n : ℕ) : Presentation ((SU3ConjugateSpinExterior.tensor.exteriorPower n).comp (projection right)) :=
  alongEquiv (restrictEquiv (exteriorConjugate n) (projection right))
    (dualComp (SU3SpinExterior.tensor.exteriorPower n) (projection right) (positive right n))

end
end Math.SU3SpinJointPresentation
