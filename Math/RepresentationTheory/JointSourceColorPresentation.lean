import Math.RepresentationTheory.JointSourcePresentation
import Math.RepresentationTheory.RestrictedColorRestriction

/-! Actual color sources at the retained joint group's color coordinate.
These transports are independent of the weak and two spin coordinates. -/
namespace Math.JointSourceColorPresentation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection JointSourcePresentation JointColorSpinWord
open SU3DefiningExterior

variable {A : Type*} [AddCommMonoid A] [Module ℂ A]

def atColor (k : RestrictedColorWordSupport.Kind) (r : Representation ℂ SU3DefiningExterior.Group A)
    (e : Representation.Equiv r (RestrictedColorWordSupport.model k).action)
    (j : JointColorSpinWord.Group →* SU3DefiningExterior.Group) (hj : ∀ g, j g=g.1) :
    Presentation (r.comp j) :=
  alongEquiv
    { toLinearEquiv := e.toLinearEquiv
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        change e (r (j g) x) = (RestrictedColorWordSupport.model k).action g.1 (e x)
        rw [← hj g]
        exact e.isIntertwining _ _ (j g) x }
    (JointSourcePresentation.color k)

def defining (j : JointColorSpinWord.Group →* SU3DefiningExterior.Group) (hj : ∀ g, j g=g.1) :
    Presentation (rho.comp j) :=
  atColor (.symmetric 1) rho (SymmetricPowerLowDegree.representationOneEquiv rho).symm j hj

def oppositeDefining (j : JointColorSpinWord.Group →* SU3DefiningExterior.Group) (hj : ∀ g, j g=g.1) :
    Presentation (rho.dual.comp j) :=
  atColor (.oppositeSymmetric 1) rho.dual
    (SymmetricPowerLowDegree.representationOneEquiv rho.dual).symm j hj

variable {K : Type*} [Group K] (c : K →* SU3DefiningExterior.Group)
  (j : JointColorSpinWord.Group →* K) (hj : ∀ g, c (j g)=g.1)

def symmetric (n : ℕ) : Presentation
    ((Representation.symmetricPower (rho.comp c) n).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.symmetric rho c n) j)
    (atColor (.symmetric n) (rho.symmetricPower n) (.refl _) (c.comp j) hj)

def oppositeSymmetric (n : ℕ) : Presentation
    ((Representation.symmetricPower (rho.dual.comp c) n).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.symmetric rho.dual c n) j)
    (atColor (.oppositeSymmetric n) (rho.dual.symmetricPower n) (.refl _) (c.comp j) hj)

def square : Presentation
    ((SymmetricSquareContractionRepresentation.action (rho.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.square rho c) j)
    (atColor .square (SymmetricSquareContractionRepresentation.action rho) (.refl _) (c.comp j) hj)

def oppositeSquare : Presentation
    ((SymmetricSquareContractionRepresentation.action (rho.dual.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.square rho.dual c) j)
    (atColor .oppositeSquare (SymmetricSquareContractionRepresentation.action rho.dual) (.refl _) (c.comp j) hj)

def cube : Presentation
    ((SymmetricCubeContractionRepresentation.action (rho.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.cube rho c) j)
    (atColor .cube (SymmetricCubeContractionRepresentation.action rho) (.refl _) (c.comp j) hj)

def oppositeCube : Presentation
    ((SymmetricCubeContractionRepresentation.action (rho.dual.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.cube rho.dual c) j)
    (atColor .oppositeCube (SymmetricCubeContractionRepresentation.action rho.dual) (.refl _) (c.comp j) hj)

def squareSquare : Presentation
    ((SymmetricSquarePartialTraceRepresentation.action (rho.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.squareSquare rho c) j)
    (atColor .squareSquare (SymmetricSquarePartialTraceRepresentation.action rho) (.refl _) (c.comp j) hj)

def oppositeSquareSquare : Presentation
    ((SymmetricSquarePartialTraceRepresentation.action (rho.dual.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.squareSquare rho.dual c) j)
    (atColor .oppositeSquareSquare (SymmetricSquarePartialTraceRepresentation.action rho.dual) (.refl _) (c.comp j) hj)

def adjoint : Presentation
    ((TraceEndomorphismSplit.traceFreeAction (rho.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.adjoint rho c) j)
    (atColor .adjoint (TraceEndomorphismSplit.traceFreeAction rho) (.refl _) (c.comp j) hj)

def oppositeAdjoint : Presentation
    ((TraceEndomorphismSplit.traceFreeAction (rho.dual.comp c)).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.adjoint rho.dual c) j)
    (atColor .oppositeAdjoint (TraceEndomorphismSplit.traceFreeAction rho.dual) (.refl _) (c.comp j) hj)

end
end Math.JointSourceColorPresentation
