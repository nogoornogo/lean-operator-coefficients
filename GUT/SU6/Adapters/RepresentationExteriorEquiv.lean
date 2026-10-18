import GUT.SU6.Characters.CertifiedConstructions

/-!
# Exterior powers preserve representation equivalences

The algebraic weight model and its Hilbert-space realization use different
copies of the defining vector space. This module connects their exterior
powers without identifying their norm or topology instances.
-/

namespace GUT.CertifiedConstructions

noncomputable section

/-- The linear equivalence induced on exterior powers. -/
def exteriorLinearEquiv
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (n : ℕ) :
    (⋀[ℂ]^n V) ≃ₗ[ℂ] (⋀[ℂ]^n W) where
  toLinearMap := exteriorPower.map n e.toLinearMap
  invFun := exteriorPower.map n e.symm.toLinearMap
  left_inv x := by
    change exteriorPower.map n e.symm.toLinearMap
      (exteriorPower.map n e.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
      LinearEquiv.symm_comp, exteriorPower.map_id, LinearMap.id_apply]
  right_inv x := by
    change exteriorPower.map n e.toLinearMap
      (exteriorPower.map n e.symm.toLinearMap x) = x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
      LinearEquiv.comp_symm, exteriorPower.map_id, LinearMap.id_apply]

/-- Equivalent actual representations have equivalent exterior powers. -/
def exteriorEquiv {R S : Actual}
    (e : Representation.Equiv R.rho S.rho) (n : ℕ) :
    Representation.Equiv (exteriorActual R n).rho (exteriorActual S n).rho :=
  .mk (exteriorLinearEquiv e.toLinearEquiv n) (by
    intro g
    change
      (exteriorPower.map n e.toLinearEquiv.toLinearMap).comp
          (exteriorPower.map n (R.rho g)) =
        (exteriorPower.map n (S.rho g)).comp
          (exteriorPower.map n e.toLinearEquiv.toLinearMap)
    rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
    exact congrArg (exteriorPower.map n) (e.toIntertwiningMap.isIntertwining' g))

/-- Transport covectors in the same direction as an equivalence by pulling
them back along its inverse. -/
def dualEquiv {R S : Actual}
    (e : Representation.Equiv R.rho S.rho) :
    Representation.Equiv (dualActual R).rho (dualActual S).rho :=
  .mk e.toLinearEquiv.symm.dualMap (by
    intro g
    change e.toLinearEquiv.symm.dualMap.toLinearMap.comp (R.rho.dual g) =
      (S.rho.dual g).comp e.toLinearEquiv.symm.dualMap.toLinearMap
    ext f x
    change f (R.rho g⁻¹ (e.symm x)) = f (e.symm (S.rho g⁻¹ x))
    exact congrArg f
      (Representation.IntertwiningMap.isIntertwining S.rho R.rho
        e.symm.toIntertwiningMap g⁻¹ x).symm)

end
end GUT.CertifiedConstructions
