import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraConnection

namespace Physics.DevMohapatraPhysicalSource
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open Math Representation DevMohapatraConnection
open scoped TensorProduct
attribute [local irreducible] DevMohapatraConnection.sourceExterior
abbrev P := DeltaBTwoModelInterface.SymmetryGroup H
abbrev Field := (SMEpsilonTensor.Color ⊗[ℂ] F) ⊗[ℂ] SixQuarkInvariant.Spin
@[reducible] local instance : AddCommGroup (Field × Field) := inferInstance
abbrev rho := (DeltaBTwoModelInterface.upModel residual).prod
  (DeltaBTwoModelInterface.downModel residual)

def reorder : (Field × Field) ≃ₗ[ℂ] (QF × QF) :=
  LinearEquiv.prodCongr DeltaBTwoFlavorBridge.reorder DeltaBTwoFlavorBridge.reorder

def source : (Field × Field) [⋀^Fin 6]→ₗ[ℂ] ℂ :=
  sourceExterior.compLinearMap reorder.toLinearMap

/-- Actual SM-cover, Lorentz and residual invariant on the physical exterior carrier. -/
def coefficient : IntertwiningMap (rho.exteriorPower 6) (Representation.trivial ℂ P ℂ) where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv source
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change sourceExterior (fun i =>
      (DeltaBTwoFlavorBridge.reorder (DeltaBTwoModelInterface.upModel residual g (v i).1),
       DeltaBTwoFlavorBridge.reorder (DeltaBTwoModelInterface.downModel residual g (v i).2))) =
      sourceExterior (fun i =>
        (DeltaBTwoFlavorBridge.reorder (v i).1,DeltaBTwoFlavorBridge.reorder (v i).2))
    simp_rw [up_action, down_action]
    exact sourceExterior_invariant g (fun i =>
      (DeltaBTwoFlavorBridge.reorder (v i).1, DeltaBTwoFlavorBridge.reorder (v i).2))

def selected : Fin 6 → QF × QF :=
  SixSlotAlternation.slots (probe 0) (probe 2) (probe 1) (probe 3) (probe 4) (probe 5)

theorem evaluation : coefficient
    (exteriorPower.ιMulti ℂ 6 (fun i => reorder.symm (selected i))) = -2 := by
  change exteriorPower.alternatingMapLinearEquiv source
    (exteriorPower.ιMulti ℂ 6 (fun i => reorder.symm (selected i))) = -2
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change sourceExterior (fun i => reorder (reorder.symm (selected i))) = -2
  simp only [LinearEquiv.apply_symm_apply]
  exact sourceExterior_evaluation

theorem nonzero : coefficient ≠ 0 := by
  intro h
  have he := evaluation
  rw [h] at he
  norm_num at he
/-- Upgrade the allowed six-quark target to the actual physical exterior carrier. -/
def domain : DevMohapatraSixQuark.Target → Type
  | .bOne => DevMohapatraSixQuark.domain .bOne
  | .sixQuark => IntertwiningMap (rho.exteriorPower 6) (Representation.trivial ℂ P ℂ)
  | .llhh => DevMohapatraSixQuark.domain .llhh

instance (t : DevMohapatraSixQuark.Target) : Zero (domain t) := by
  cases t <;> unfold domain <;> infer_instance

theorem satisfies : MixedSelectionRequests.Satisfies domain DevMohapatraSixQuark.request := by
  constructor
  · intro t ht; change t = .bOne at ht; subst t
    exact DevMohapatraSixQuark.satisfies.1 _ rfl
  · intro t ht
    rcases ht with rfl | rfl
    · exact ⟨coefficient,nonzero⟩
    · exact DevMohapatraSixQuark.satisfies.2 _ (Or.inr rfl)

end
end Physics.DevMohapatraPhysicalSource
