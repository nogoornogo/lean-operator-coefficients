import Physics.StandardModel.Operators.Dipole.DipoleMediatorPaths
import Physics.StandardModel.Operators.Dipole.DipoleControls

open Math

/-! Two opposing mediator paths with nonlinear square weights. An algebraic
sample only: no UV matching, mass-basis identification or photon amplitude. -/
namespace Physics.DipoleMediatorControls
set_option autoImplicit false
noncomputable section
open Representation DipoleControls

def incoming (_ : Fin 2) : IntertwiningMap flavor flavor := IntertwiningMap.id flavor
def outgoing (i : Fin 2) : IntertwiningMap flavor flavor :=
  if i = 0 then bridge else -bridge
def weakOutgoing (_ : Fin 2) : IntertwiningMap flavor flavor := 0
def weights (x : Fin 2 → ℂ) (i : Fin 2) : ℂ := (x i)^2

def generation (x : Fin 2 → ℂ) : DipoleFlavorSelection.Coefficients flavor flavor :=
  DipoleMediatorPaths.generation flavor flavor flavor incoming outgoing weakOutgoing weights x

theorem weights_isolate : WeightedSelectedPaths.Isolates weights :=
  WeightedSelectedPaths.squares_isolate

theorem selected (x : Fin 2 → ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron (generation x) =
    ((x 0)^2 - (x 1)^2, 0) := by
  rw [generation, DipoleMediatorPaths.selected]
  simp [weights, incoming, outgoing, weakOutgoing, Fin.sum_univ_two, sub_eq_add_neg]

theorem nonzero_iff (x : Fin 2 → ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron (generation x) ≠ 0 ↔
    (x 0)^2 ≠ (x 1)^2 := by
  rw [selected]
  simp [sub_eq_zero]

theorem each_path_nonzero (i : Fin 2) :
    electron (outgoing i (incoming i mu)) ≠ 0 := by
  simp only [incoming, IntertwiningMap.id_apply, outgoing]
  split_ifs <;> simp

theorem cancellation :
    DipoleFlavorSelection.selector flavor flavor mu electron
      (generation (fun _ => 1)) = 0 := by
  rw [selected]
  simp

/-- Restricting the domain to equal coordinates removes every nonzero input,
despite both mediator paths having nonzero selected composites. -/
theorem restricted_family_vanishes (z : ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron
      (generation (fun _ => z)) = 0 := by
  rw [selected]
  simp

theorem realized : ∃ x, DipoleFlavorSelection.selector flavor flavor mu electron
    (generation x) ≠ 0 := by
  apply (DipoleMediatorPaths.exists_nonzero_iff_path flavor flavor flavor
    incoming outgoing weakOutgoing weights mu electron weights_isolate).mpr
  exact ⟨0, Or.inl (each_path_nonzero 0)⟩

end
end Physics.DipoleMediatorControls
