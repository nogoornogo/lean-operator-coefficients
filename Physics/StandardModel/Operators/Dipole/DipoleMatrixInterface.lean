import Physics.StandardModel.Operators.Dipole.DipoleModelInterface
import Math.RepresentationTheory.Invariants.MatrixIntertwiner

open Math

/-! Finite matrix registration using supplied flavor coordinates and equivariance. -/
namespace Physics.DipoleMatrixInterface
set_option autoImplicit false
noncomputable section
open Representation

variable {H J K X : Type*} [Group H] [Fintype J] [Fintype K]
  [DecidableEq J] [DecidableEq K]
  (a : Representation ℂ H (J → ℂ)) (b : Representation ℂ H (K → ℂ))

def register (domain : Set X) (mu : J) (e : K) (cB cW : X → Matrix K J ℂ)
    (hB : ∀ x g v, (cB x).mulVec (a g v) = b g ((cB x).mulVec v))
    (hW : ∀ x g v, (cW x).mulVec (a g v) = b g ((cW x).mulVec v)) :
    DipoleModelInterface.Registered (X := X) a b :=
  DipoleModelInterface.ofResidual a b domain (Pi.single mu 1)
    ((Pi.basisFun ℂ K).coord e)
    (fun x => (MatrixIntertwiner.ofMatrix a b (cB x) (hB x),
      MatrixIntertwiner.ofMatrix a b (cW x) (hW x)))

omit [DecidableEq K] in
theorem selected_entry (domain : Set X) (mu : J) (e : K) (cB cW : X → Matrix K J ℂ)
    (hB : ∀ x g v, (cB x).mulVec (a g v) = b g ((cB x).mulVec v))
    (hW : ∀ x g v, (cW x).mulVec (a g v) = b g ((cW x).mulVec v))
    (x : X) (hx : x ∈ domain) :
    (register a b domain mu e cB cW hB hW).observe x = (cB x e mu, cW x e mu) := by
  rw [DipoleModelInterface.Registered.selected _ x hx]
  simp only [register, DipoleModelInterface.ofResidual, Module.Basis.coord_apply,
    Pi.basisFun_repr, MatrixIntertwiner.entry]

end
end Physics.DipoleMatrixInterface
