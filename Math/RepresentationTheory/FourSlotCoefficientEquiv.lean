import Math.RepresentationTheory.FourSlotRestrictionLift

/-! Independent degree-(2,1,1) exterior Hom equals ordered Hom with its
explicit first-two-slot antisymmetry. -/
namespace Math.FourSlotCoefficientEquiv
set_option autoImplicit false
noncomputable section
open Representation FourSlotAlternation FourSlotSpeciesDegree FourSlotRestrictionLift
open scoped TensorProduct
variable {H A B C : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (c : Representation ℂ H C)

abbrev Ordered := IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ)

def swap : Representation.Equiv ((a.tprod a).tprod (b.tprod c))
    ((a.tprod a).tprod (b.tprod c)) where
  toLinearEquiv := TensorProduct.congr (TensorProduct.comm ℂ A A) (LinearEquiv.refl ℂ (B ⊗[ℂ] C))
  isIntertwining' g := by ext x y u e; rfl

def antisymmetric : Submodule ℂ (Ordered a b c) where
  carrier := {f | ∀ x y u e, f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
    -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x y u e; change f _ + g _ = -(f _ + g _); rw [hf,hg,neg_add]
  smul_mem' := by intro z f hf x y u e; change z • f _ = -(z • f _); rw [hf,smul_neg]

theorem mem_antisymmetric_iff (f : Ordered a b c) : f ∈ antisymmetric a b c ↔
    f.comp (swap a b c).toIntertwiningMap = -f := by
  constructor
  · intro h
    apply IntertwiningMap.ext
    ext x y u e
    exact h x y u e
  · intro h x y u e
    exact DFunLike.congr_fun h ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))

def toOrdered (f : sector a b c) : antisymmetric a b c :=
  ⟨restriction a b c f.val, restriction_swap a b c f.val⟩

def toExterior (f : antisymmetric a b c) : sector a b c :=
  ⟨coefficient a b c ((1/2 : ℂ) • f.val), coefficient_hasDegree a b c _⟩

def equiv : sector a b c ≃ₗ[ℂ] antisymmetric a b c where
  toFun := toOrdered a b c
  invFun := toExterior a b c
  left_inv f := by apply Subtype.ext; exact reconstruct a b c f.val f.property
  right_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    ext x y u e
    change restriction a b c (coefficient a b c ((1/2 : ℂ) • f.val))
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) = f.val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e))
    rw [show restriction a b c (coefficient a b c ((1/2 : ℂ) • f.val))
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      coefficient a b c ((1/2 : ℂ) • f.val) (exteriorPower.ιMulti ℂ 4 (slots x y u e)) from rfl,
      coefficient_slots]
    change (1/2 : ℂ) * f.val _ - (1/2 : ℂ) * f.val _ = f.val _
    rw [f.property x y u e]
    ring
  map_add' f g := by apply Subtype.ext; apply IntertwiningMap.ext; ext x y u e; rfl
  map_smul' z f := by apply Subtype.ext; apply IntertwiningMap.ext; ext x y u e; rfl

end
end Math.FourSlotCoefficientEquiv
