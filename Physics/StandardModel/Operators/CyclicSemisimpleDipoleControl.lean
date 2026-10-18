import Physics.StandardModel.Operators.SemisimpleDipoleSelection
import Physics.StandardModel.Operators.CyclicSelectorDipoleSelection
import Math.RepresentationTheory.Decomposition.ScalarIrreducible

namespace GUT.CyclicSemisimpleDipoleControl
set_option autoImplicit false
noncomputable section
open Math Representation
variable {k : ℕ} [NeZero k] {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] (a : I → ZMod k) (b : J → ZMod k)

local instance (i : I) : IsIrreducible (CyclicCharge.representation (a i)) :=
  ScalarIrreducible.irreducible _
local instance (j : J) : IsIrreducible (CyclicCharge.representation (b j)) :=
  ScalarIrreducible.irreducible _

def decomposition (a : I → ZMod k) : Representation.Equiv (CyclicWeightCoordinates.diagonal a)
    (FiniteBlockHom.action (fun i => CyclicCharge.representation (a i))) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by ext x i; rfl

theorem control (mu : I → ℂ) (ell : Module.Dual ℂ (J → ℂ)) :
    (∃ p : IrreducibleBlockCoordinates.Match
        (fun i => CyclicCharge.representation (a i)) (fun j => CyclicCharge.representation (b j)),
      ell (SemisimpleDipoleSelection.matrixUnit _ _ (decomposition a) (decomposition b) p mu) ≠ 0) ↔
    CyclicSelectorDipoleSelection.SupportedMatch a b mu ell := by
  rw [← SemisimpleDipoleSelection.selected_allowed_iff _ _ (decomposition a) (decomposition b)]
  exact CyclicSelectorDipoleSelection.selected_allowed_iff a b mu ell
end
end GUT.CyclicSemisimpleDipoleControl
