import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Basic.Complex.Basic

/-! Descent of an actual representation along a surjective group map.
The kernel condition is checked in applications, not a realization axiom. -/

set_option autoImplicit false

namespace Math.RepresentationDescent

noncomputable section

variable {G K V W : Type*} [Group G] [Group K]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  (q : G →* K) (hq : Function.Surjective q) (rho : Representation ℂ G V)
  (hk : q.ker ≤ rho.ker)

def descend : Representation ℂ K V :=
  (Units.coeHom (V →ₗ[ℂ] V)).comp
    (q.liftOfSurjective hq ⟨rho.asGroupHom, fun g hg => by
      apply Units.ext
      exact hk hg⟩)

@[simp] theorem descend_apply (g : G) : descend q hq rho hk (q g) = rho g := by
  simp [descend, MonoidHom.liftOfSurjective, Representation.asGroupHom_apply]

theorem descend_comp : (descend q hq rho hk).comp q = rho := by
  ext g v
  exact congrArg (fun f => f v) (descend_apply q hq rho hk g)

theorem descend_invariant (f : V →ₗ[ℂ] ℂ) (hf : ∀ g v, f (rho g v) = f v) :
    ∀ k v, f (descend q hq rho hk k v) = f v := by
  intro k v
  obtain ⟨g, rfl⟩ := hq k
  rw [descend_apply]
  exact hf g v

include hk in
theorem kernel_dual : q.ker ≤ rho.dual.ker := by
  intro g hg
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro v
  change phi (rho g⁻¹ v) = phi v
  rw [show rho g⁻¹ = 1 from hk (q.ker.inv_mem hg)]
  rfl

include hk in
theorem kernel_tensor (sigma : Representation ℂ G W) (hs : q.ker ≤ sigma.ker) :
    q.ker ≤ (rho.tprod sigma).ker := by
  intro g hg
  change TensorProduct.map (rho g) (sigma g) = 1
  rw [show rho g = 1 from hk hg, show sigma g = 1 from hs hg]
  exact TensorProduct.map_one

end

end Math.RepresentationDescent
