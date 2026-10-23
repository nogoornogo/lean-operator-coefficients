import Math.RepresentationTheory.Exterior.SymmetricSquareCauchy

/-! The symmetric square of the scalar trivial representation is the
scalar line, by multiplication and its actual inverse. -/
namespace Math.ScalarSymmetricSquare
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients Representation

def multiply : Sym[ℂ]^2 ℂ →ₗ[ℂ] ℂ :=
  symmetricLift (TensorProduct.lid ℂ ℂ).toLinearMap (by
    intro x y
    exact mul_comm y x)

theorem multiply_pure (x y : ℂ) : multiply (sym (x ⊗ₜ[ℂ] y))=x*y :=
  symmetricLift_pure _ _ x y

theorem pure (x y : ℂ) : sym (x ⊗ₜ[ℂ] y)=(x*y) • sym ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) := by
  have ht : (x ⊗ₜ[ℂ] y)=(x*y) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) := by
    apply (TensorProduct.lid ℂ ℂ).injective
    simp
  rw [ht, map_smul]

def linearEquivalence : Sym[ℂ]^2 ℂ ≃ₗ[ℂ] ℂ where
  toLinearMap := multiply
  invFun z := z • sym ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  left_inv x := by
    have h : ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (sym ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)))).comp
        multiply=LinearMap.id := by
      apply SymmetricPower.ext
      intro v
      rw [← sym_eta v]
      change multiply (sym (v 0 ⊗ₜ[ℂ] v 1)) • sym ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))=
        sym (v 0 ⊗ₜ[ℂ] v 1)
      rw [multiply_pure]
      exact (pure _ _).symm
    exact LinearMap.congr_fun h x
  right_inv z := by
    change multiply (z • sym ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)))=z
    rw [map_smul, multiply_pure]
    simp

def equivalence (G : Type*) [Group G] : Representation.Equiv
    ((trivial ℂ G ℂ).symmetricPower 2) (trivial ℂ G ℂ) where
  toLinearEquiv := linearEquivalence
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro v
    simp only [LinearMap.comp_apply, Representation.symmetricPower_apply_tprod]
    rfl

end
end Math.ScalarSymmetricSquare
