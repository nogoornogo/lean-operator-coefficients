import Physics.StandardModel.Operators.Weinberg.WeinbergMajorana
import Physics.FieldTheory.Mass.Algebra.WeylMassTwoTorsion

/-! One-dimensional flavor controls, including nontrivial order-two residual charge. -/
namespace Physics.WeinbergScalarFlavor
set_option autoImplicit false
noncomputable section
open Representation WeinbergResidualHom
open scoped TensorProduct
variable {R : Type*} [Group R] (a : Representation ℂ R ℂ)

theorem scalar_formula (f : Residual a) (x y : ℂ) :
    f (x ⊗ₜ[ℂ] y) = x * y * f (1 ⊗ₜ[ℂ] 1) := by
  calc
    _ = f ((x • (1 : ℂ)) ⊗ₜ[ℂ] (y • (1 : ℂ))) := by simp
    _ = _ := by rw [TensorProduct.smul_tmul_smul, map_smul]; rfl

def scalarCoefficient (ha : ∀ r, (a r 1) ^ 2 = 1) :
    WeinbergMajorana.MassCoefficients a :=
  ⟨{ toLinearMap := TensorProduct.lift (LinearMap.mul ℂ ℂ)
     isIntertwining' r := by
       apply TensorProduct.ext'
       intro x y
       change a r x * a r y = x * y
       have hx : a r x = x * a r 1 := by
         simpa using (a r).map_smul x (1 : ℂ)
       have hy : a r y = y * a r 1 := by
         simpa using (a r).map_smul y (1 : ℂ)
       rw [hx, hy]
       calc
         _ = (x * y) * (a r 1) ^ 2 := by ring
         _ = x * y := by rw [ha]; ring }, fun x y => mul_comm y x⟩

def scalarEquiv (ha : ∀ r, (a r 1) ^ 2 = 1) :
    WeinbergMajorana.MassCoefficients a ≃ₗ[ℂ] ℂ where
  toFun f := f.val (1 ⊗ₜ[ℂ] 1)
  invFun z := z • scalarCoefficient a ha
  left_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change f.val (1 ⊗ₜ[ℂ] 1) * (x * y) = f.val (x ⊗ₜ[ℂ] y)
    rw [scalar_formula a f.val x y]
    ring
  right_inv z := by change z * (1 * 1) = z; ring
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nonzero_iff_square_trivial : (∃ f : sector a, f ≠ 0) ↔
    ∀ r, (a r 1) ^ 2 = 1 := by
  constructor
  · rintro ⟨f, hf⟩ r
    let k := (symmetricEquiv a f).val
    have hk : k (1 ⊗ₜ[ℂ] 1) ≠ 0 := by
      intro hz
      apply hf
      apply (symmetricEquiv a).injective
      apply Subtype.ext
      apply IntertwiningMap.ext
      apply TensorProduct.ext'
      intro x y
      change k (x ⊗ₜ[ℂ] y) = 0
      rw [scalar_formula, hz, mul_zero]
    have hi := IntertwiningMap.isIntertwining _ _ k r (1 ⊗ₜ[ℂ] 1)
    change k (a r 1 ⊗ₜ[ℂ] a r 1) = k (1 ⊗ₜ[ℂ] 1) at hi
    rw [scalar_formula, ← pow_two] at hi
    exact (mul_right_cancel₀ hk (hi.trans (one_mul _).symm))
  · intro ha
    let e := (symmetricEquiv a).trans (scalarEquiv a ha)
    refine ⟨e.symm 1, ?_⟩
    intro hz
    have h := congrArg e hz
    simp at h

def oneGenerationEquiv : sector (Representation.trivial ℂ R ℂ) ≃ₗ[ℂ] ℂ :=
  (symmetricEquiv _).trans (scalarEquiv _ (by intro r; norm_num))

theorem oneGeneration_finrank :
    Module.finrank ℂ (sector (Representation.trivial ℂ R ℂ)) = 1 := by
  rw [oneGenerationEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem sign_allowed : ∃ f : sector WeylMassTwoTorsion.signRepresentation, f ≠ 0 := by
  apply (exists_nonzero_iff_square_trivial _).mpr
  intro r
  obtain rfl | rfl := Int.units_eq_one_or r <;> norm_num
    [WeylMassTwoTorsion.signRepresentation_apply]

end
end Physics.WeinbergScalarFlavor
