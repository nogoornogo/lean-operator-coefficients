import Math.LinearAlgebra.ExteriorNaturality
import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

/-! Exterior functoriality for a polarized Clifford action. The second
isotropic summand transforms contragrediently via the polar pairing. -/

set_option autoImplicit false

namespace Math.PolarizedExteriorAction

noncomputable section

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : TauCeti.SpinPolarizationData Q)

def dualAction (e : P.W ≃ₗ[K] P.W) : P.W' ≃ₗ[K] P.W' :=
  P.pairingEquiv.trans (e.symm.dualMap.trans P.pairingEquiv.symm)

theorem dualAction_pairing (e : P.W ≃ₗ[K] P.W) (y : P.W') :
    P.pairingEquiv (dualAction P e y) = (P.pairingEquiv y).comp e.symm.toLinearMap := by
  ext x
  simp [dualAction]

def vectorAction (e : P.W ≃ₗ[K] P.W) : V ≃ₗ[K] V :=
  P.decompositionEquiv.symm.trans
    (((e.prodCongr (dualAction P e)).prodCongr (LinearEquiv.refl K P.line)).trans
      P.decompositionEquiv)

@[simp] theorem vectorAction_W (e : P.W ≃ₗ[K] P.W) (x : P.W) :
    vectorAction P e (x : V) = (e x : V) := by simp [vectorAction]

@[simp] theorem vectorAction_W' (e : P.W ≃ₗ[K] P.W) (y : P.W') :
    vectorAction P e (y : V) = (dualAction P e y : V) := by simp [vectorAction]

theorem cliffordOperator_naturality (hline : P.line = ⊥) (e : P.W ≃ₗ[K] P.W)
    (v : V) (s : ExteriorAlgebra K P.W) :
    ExteriorNaturality.mapEquiv e (P.cliffordOperator v s) =
      P.cliffordOperator (vectorAction P e v) (ExteriorNaturality.mapEquiv e s) := by
  obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := P.decompositionEquiv.surjective v
  have hz : (z : V) = 0 := Submodule.mem_bot K |>.mp (hline ▸ z.property)
  rw [P.decompositionEquiv_apply, hz, add_zero]
  simp only [map_add, LinearMap.add_apply, vectorAction_W, vectorAction_W',
    P.cliffordOperator_coe_W, P.cliffordOperator_coe_W', P.wedge_apply, P.contract_apply]
  rw [ExteriorNaturality.mapEquiv_creation, ExteriorNaturality.mapEquiv_contract,
    dualAction_pairing]

end

end Math.PolarizedExteriorAction
