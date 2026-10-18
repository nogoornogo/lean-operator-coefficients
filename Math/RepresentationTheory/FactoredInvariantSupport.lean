import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.LinearAlgebra.SelectionCriteria

/-! Extend an invariant functional across an additional trivially acting factor. -/
namespace Math.FactoredInvariantSupport
set_option autoImplicit false
noncomputable section
open Representation
variable {G K Z V : Type*} [Group G] [Group K] [Group Z]
  [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V) (j : K →* G) (z : Z →* G)
  (hd : ∀ g, ∃ k t, g = j k * z t) (hz : ∀ t x, rho (z t) x = x)

def extend (f : InvariantCoefficientTransport.Invariants (rho.comp j)) :
    InvariantCoefficientTransport.Invariants rho where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    obtain ⟨k,t,he⟩ := hd g
    change f (rho g x) = f x
    rw [he, map_mul, Module.End.mul_apply, hz]
    exact f.isIntertwining _ _ k x

include z hd hz in
theorem allowed (h : SelectionCriteria.Allowed
    (InvariantCoefficientTransport.Invariants (rho.comp j))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants rho) := by
  obtain ⟨f,hf⟩ := h
  refine ⟨extend rho j z hd hz f, ?_⟩
  intro he
  apply hf
  ext x
  exact DFunLike.congr_fun he x

end
end Math.FactoredInvariantSupport
