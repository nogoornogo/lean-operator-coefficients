import Math.RepresentationTheory.JointSourcePresentation
import Math.RepresentationTheory.RestrictedColorRestriction

/-! Place an actual symmetric SU2 source at its fixed weak, left or right
coordinate, preserving the independent actions in each case. -/
namespace Math.JointSourceSpinPresentation
set_option autoImplicit false
noncomputable section
open Representation JointSourcePresentation JointColorSpinWord SplitRepresentationProjection

def atWeak (n : ℕ) (j : JointColorSpinWord.Group →* TauCeti.SU2) (hj : ∀ g, j g=g.2.1) :
    Presentation ((WeakDoubletScalars.doublet.symmetricPower n).comp j) :=
  alongEquiv
    { toLinearEquiv := .refl ℂ _
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact congrArg (fun k => WeakDoubletScalars.doublet.symmetricPower n k x) (hj g) }
    (JointSourcePresentation.weak n)

def atLeft (n : ℕ) (j : JointColorSpinWord.Group →* TauCeti.SU2) (hj : ∀ g, j g=g.2.2.1) :
    Presentation ((WeakDoubletScalars.doublet.symmetricPower n).comp j) :=
  alongEquiv
    { toLinearEquiv := .refl ℂ _
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact congrArg (fun k => WeakDoubletScalars.doublet.symmetricPower n k x) (hj g) }
    (JointSourcePresentation.leftSpin n)

def atRight (n : ℕ) (j : JointColorSpinWord.Group →* TauCeti.SU2) (hj : ∀ g, j g=g.2.2.2) :
    Presentation ((WeakDoubletScalars.doublet.symmetricPower n).comp j) :=
  alongEquiv
    { toLinearEquiv := .refl ℂ _
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact congrArg (fun k => WeakDoubletScalars.doublet.symmetricPower n k x) (hj g) }
    (JointSourcePresentation.rightSpin n)

def weakDoublet (j : JointColorSpinWord.Group →* TauCeti.SU2) (hj : ∀ g, j g=g.2.1) :
    Presentation (WeakDoubletScalars.doublet.comp j) :=
  alongEquiv (restrictEquiv (SymmetricPowerLowDegree.representationOneEquiv WeakDoubletScalars.doublet).symm j)
    (atWeak 1 j hj)

def leftDoublet (j : JointColorSpinWord.Group →* TauCeti.SU2) (hj : ∀ g, j g=g.2.2.1) :
    Presentation (WeakDoubletScalars.doublet.comp j) :=
  alongEquiv (restrictEquiv (SymmetricPowerLowDegree.representationOneEquiv WeakDoubletScalars.doublet).symm j)
    (atLeft 1 j hj)

def rightDoublet (j : JointColorSpinWord.Group →* TauCeti.SU2) (hj : ∀ g, j g=g.2.2.2) :
    Presentation (WeakDoubletScalars.doublet.comp j) :=
  alongEquiv (restrictEquiv (SymmetricPowerLowDegree.representationOneEquiv WeakDoubletScalars.doublet).symm j)
    (atRight 1 j hj)

def pulledWeak (n : ℕ) {K : Type*} [Group K] (c : K →* TauCeti.SU2)
    (j : JointColorSpinWord.Group →* K) (hj : ∀ g, c (j g)=g.2.1) :
    Presentation ((Representation.symmetricPower (WeakDoubletScalars.doublet.comp c) n).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.symmetric WeakDoubletScalars.doublet c n) j)
    (atWeak n (c.comp j) hj)

def pulledLeft (n : ℕ) {K : Type*} [Group K] (c : K →* TauCeti.SU2)
    (j : JointColorSpinWord.Group →* K) (hj : ∀ g, c (j g)=g.2.2.1) :
    Presentation ((Representation.symmetricPower (WeakDoubletScalars.doublet.comp c) n).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.symmetric WeakDoubletScalars.doublet c n) j)
    (atLeft n (c.comp j) hj)

def pulledRight (n : ℕ) {K : Type*} [Group K] (c : K →* TauCeti.SU2)
    (j : JointColorSpinWord.Group →* K) (hj : ∀ g, c (j g)=g.2.2.2) :
    Presentation ((Representation.symmetricPower (WeakDoubletScalars.doublet.comp c) n).comp j) :=
  alongEquiv (restrictEquiv (RestrictedColorRestriction.symmetric WeakDoubletScalars.doublet c n) j)
    (atRight n (c.comp j) hj)

def scalarComp {K : Type*} [Group K] (j : JointColorSpinWord.Group →* K) :
    Presentation ((trivial ℂ K ℂ).comp j) :=
  alongEquiv { toLinearEquiv := .refl ℂ _, isIntertwining' _ := rfl } JointSourcePresentation.scalar

end
end Math.JointSourceSpinPresentation
