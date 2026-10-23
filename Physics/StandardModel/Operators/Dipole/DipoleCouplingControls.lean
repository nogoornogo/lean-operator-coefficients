import Physics.StandardModel.Operators.Dipole.DipoleCouplingModel
import Physics.StandardModel.Operators.Dipole.DipoleControls

/-! Scalar-coupling controls, not physical UV matching examples. -/
namespace Physics.DipoleCouplingControls
set_option autoImplicit false
noncomputable section
open Representation DipoleControls

def model (t : ℂ) : DipoleCouplingModel.Couplings (X := ℂ) (Y := ℂ) flavor flavor flavor where
  incoming := (_root_.LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (IntertwiningMap.id flavor)
  outgoingB := (_root_.LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight bridge
  outgoingW := 0
  propagator := t • IntertwiningMap.id flavor

theorem selected (t x y : ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron
      (DipoleCouplingModel.generation flavor flavor flavor (model t) x y) = (x*y*t,0) := by
  rw [DipoleCouplingModel.selected]
  apply Prod.ext
  · simp [model]
    ring
  · simp [model]

theorem nonzero_iff (t x y : ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron
      (DipoleCouplingModel.generation flavor flavor flavor (model t) x y) ≠ 0 ↔
    x ≠ 0 ∧ y ≠ 0 ∧ t ≠ 0 := by
  rw [selected]
  simp [and_assoc]

theorem zero_propagator (x y : ℂ) :
    DipoleCouplingModel.generation flavor flavor flavor (model 0) x y = 0 := by
  apply DipoleCouplingModel.generation_zero_of_propagator_zero
  simp [model]

theorem nonlinear_pullback (z : ℂ) :
    DipoleFlavorSelection.selector flavor flavor mu electron
      (DipoleCouplingModel.generation flavor flavor flavor (model 1) (z^2) z) = (z^3,0) := by
  rw [selected]
  apply Prod.ext
  · ring
  · rfl

end
end Physics.DipoleCouplingControls
