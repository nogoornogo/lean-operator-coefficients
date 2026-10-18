import Math.RepresentationTheory.TopExteriorCauchy

/-! Tensoring with a normalized invariant vector preserves injectivity. -/
namespace Math.InvariantVectorInjection
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def map (r : Representation ℂ G V) (s : Representation ℂ G W)
    (v : W) (hv : ∀ g, s g v = v) : IntertwiningMap r (r.tprod s) where
  toLinearMap := (TensorProduct.mk ℂ V W).flip v
  isIntertwining' g := by
    ext x
    change r g x ⊗ₜ[ℂ] v = r g x ⊗ₜ[ℂ] s g v
    rw [hv]

theorem injective (r : Representation ℂ G V) (s : Representation ℂ G W)
    (v : W) (hv : ∀ g, s g v = v) (φ : Module.Dual ℂ W) (hφ : φ v = 1) :
    Function.Injective (map r s v hv) := by
  intro x y h
  have he := congrArg (TopExteriorCauchy.evaluate (A := V) φ) h
  simpa only [map, IntertwiningMap.coe_mk, LinearMap.flip_apply, TensorProduct.mk_apply,
    TopExteriorCauchy.evaluate_tmul, hφ, one_smul] using he

end
end Math.InvariantVectorInjection
