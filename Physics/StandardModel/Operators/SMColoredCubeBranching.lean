import Physics.StandardModel.Operators.SMColoredCoreBranching
import Math.RepresentationTheory.SU3SpinExteriorCube
import Math.RepresentationTheory.SU3ConjugateSpinExteriorCube

/-! The complete middle exterior degree of actual signed U/D cores.
All color and spin actions are retained; charge/Higgs permissions and
couplings between several cores are separate consumer obligations. -/
namespace GUT.SMColoredCubeBranching
set_option autoImplicit false
noncomputable section
open Representation Math SMColoredCoreBranching

/-- Actual U/D degree-three branching, with the full retained group action. -/
def positiveCube (s : DeltaLOneSignedInput.Species) (hs : s=1 ∨ s=2) :
    Representation.Equiv ((core s).exteriorPower 3)
      ((SU3SpinExteriorCube.topBranch.prod SU3SpinExteriorCube.middleBranch).comp (projection true)) :=
  (positiveExteriorEquiv s hs 3).trans
    (SplitRepresentationProjection.restrictEquiv SU3SpinExteriorCube.cubeEquiv (projection true))

/-- Actual conjugate U/D degree-three branching, retaining the other spin. -/
def negativeCube (s : DeltaLOneSignedInput.Species) (hs : s=6 ∨ s=7) :
    Representation.Equiv ((core s).exteriorPower 3)
      ((SU3ConjugateSpinExteriorCube.topBranch.prod SU3ConjugateSpinExteriorCube.middleBranch).comp
        (projection false)) :=
  (negativeExteriorEquiv s hs 3).trans
    (SplitRepresentationProjection.restrictEquiv SU3ConjugateSpinExteriorCube.cubeEquiv (projection false))

end
end GUT.SMColoredCubeBranching
