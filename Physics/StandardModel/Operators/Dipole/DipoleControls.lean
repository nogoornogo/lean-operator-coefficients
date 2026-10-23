import Physics.StandardModel.Operators.Dipole.DipoleFlavorSelection

open Math

/-! Exact two-flavor controls. These are algebraic samples, not a UV model
or a matching calculation. -/
namespace Physics.DipoleControls
set_option autoImplicit false
noncomputable section
open Representation TwoComponentTensorUniqueness

abbrev Flavor := Fin 2 → ℂ
def flavor : Representation ℂ Unit Flavor := Representation.trivial ℂ Unit Flavor
def mu : Flavor := basis2 1
def electron : Module.Dual ℂ Flavor := (Pi.basisFun ℂ (Fin 2)).coord 0

def bridge : IntertwiningMap flavor flavor where
  toLinearMap := ((Pi.basisFun ℂ (Fin 2)).coord 1).smulRight (basis2 0)
  isIntertwining' _ := rfl

@[simp] theorem bridge_selected : electron (bridge mu) = 1 := by
  simp [electron, bridge, mu, basis2, Module.Basis.coord_apply]

@[simp] theorem diagonal_selected : electron (IntertwiningMap.id flavor mu) = 0 := by
  simp [electron, mu, basis2, Module.Basis.coord_apply]

def generation (z : ℂ) : DipoleFlavorSelection.Coefficients flavor flavor :=
  (DipoleSMCoefficient.equiv flavor flavor).symm (z^2 • bridge, 0)

@[simp] theorem generation_selected (z : ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron (generation z) = (z^2,0) := by
  change (electron (((DipoleSMCoefficient.equiv flavor flavor)
    ((DipoleSMCoefficient.equiv flavor flavor).symm (z^2 • bridge, 0))).1 mu),
    electron (((DipoleSMCoefficient.equiv flavor flavor)
    ((DipoleSMCoefficient.equiv flavor flavor).symm (z^2 • bridge, 0))).2 mu)) = _
  simp

theorem generation_nonzero_iff (z : ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron (generation z) ≠ 0 ↔ z ≠ 0 := by
  rw [generation_selected]
  simp

theorem generation_not_additive : generation (1+1) ≠ generation 1 + generation 1 := by
  intro h
  have he := congrArg (DipoleFlavorSelection.selector flavor flavor mu electron) h
  rw [map_add, generation_selected, generation_selected] at he
  have hfirst := congrArg Prod.fst he
  norm_num at hfirst

theorem allowed_not_realized_by_zero :
    (∃ c : DipoleFlavorSelection.Coefficients flavor flavor,
      DipoleFlavorSelection.selector flavor flavor mu electron c ≠ 0) ∧
    ¬ ∃ x : Unit, DipoleFlavorSelection.selector flavor flavor mu electron
      ((fun _ => 0) x) ≠ 0 := by
  constructor
  · exact DipoleFlavorSelection.allowed_of_bridge flavor flavor mu electron bridge
      (by rw [bridge_selected]; exact one_ne_zero)
  · simp

end
end Physics.DipoleControls
