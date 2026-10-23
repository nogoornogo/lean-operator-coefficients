import Math.RepresentationTheory.Invariants.InvariantQuadraticPowers

namespace Math.MixedInvariantDressing
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G F B : Type*} [Group G] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup B] [Module ℂ B]
  {a : Representation ℂ G F} {b : Representation ℂ G B}

def product (f : IntertwiningMap a (trivial ℂ G ℂ))
    (g : IntertwiningMap b (trivial ℂ G ℂ)) :
    IntertwiningMap (a.tprod b) (trivial ℂ G ℂ) :=
  (Representation.TensorProduct.rid ℂ (trivial ℂ G ℂ)).toIntertwiningMap.comp
    (IntertwiningMap.tensor f g)

@[simp] theorem product_apply (f : IntertwiningMap a (trivial ℂ G ℂ))
    (g : IntertwiningMap b (trivial ℂ G ℂ)) (x : F) (y : B) :
    product f g (x ⊗ₜ[ℂ] y) = f x * g y := by simp [product,mul_comm]

def productLinearRight (g : IntertwiningMap b (trivial ℂ G ℂ)) :
    IntertwiningMap a (trivial ℂ G ℂ) →ₗ[ℂ] IntertwiningMap (a.tprod b) (trivial ℂ G ℂ) where
  toFun f := product f g
  map_add' f h := by
    apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change product (f+h) g (x ⊗ₜ[ℂ] y) = product f g (x ⊗ₜ[ℂ] y)+product h g (x ⊗ₜ[ℂ] y)
    rw [product_apply,product_apply,product_apply]
    change (f x+h x)*g y = f x*g y+h x*g y
    ring
  map_smul' z f := by
    apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change product (z • f) g (x ⊗ₜ[ℂ] y) = z • product f g (x ⊗ₜ[ℂ] y)
    rw [product_apply,product_apply]
    change (z*f x)*g y = z*(f x*g y)
    ring

theorem product_nonzero (f : IntertwiningMap a (trivial ℂ G ℂ))
    (g : IntertwiningMap b (trivial ℂ G ℂ)) (hf : f ≠ 0) (hg : g ≠ 0) :
    product f g ≠ 0 := by
  have hx : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    have hz : ∀ x, f x = 0 := by simpa only [not_exists,not_not] using h
    exact hz x
  have hy : ∃ y, g y ≠ 0 := by
    by_contra h
    apply hg
    ext y
    have hz : ∀ y, g y = 0 := by simpa only [not_exists,not_not] using h
    exact hz y
  obtain ⟨x,hx⟩ := hx
  obtain ⟨y,hy⟩ := hy
  intro h
  have he := congrArg (fun c : IntertwiningMap (a.tprod b) (trivial ℂ G ℂ) =>
    c (x ⊗ₜ[ℂ] y)) h
  exact (mul_ne_zero hx hy) (by simpa using he)
end
end Math.MixedInvariantDressing
