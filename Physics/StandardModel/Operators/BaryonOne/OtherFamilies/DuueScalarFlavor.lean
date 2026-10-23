import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueResidualCompleteness

/-! One-dimensional multiplicity controls for duue, with arbitrary residual
characters rather than an assumed neutral input. -/
namespace Physics.DuueScalarFlavor
set_option autoImplicit false
noncomputable section
open Representation DuueOrderedCompleteness
open scoped TensorProduct
variable {R : Type*} [Group R] (u d e : Representation ℂ R ℂ)

theorem scalar_formula (f : Residual u d e) (x y h j : ℂ) :
    f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) =
      (x * y) * (h * j) * f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) := by
  calc
    _ = f (((x • (1 : ℂ)) ⊗ₜ[ℂ] (y • (1 : ℂ))) ⊗ₜ[ℂ]
      ((h • (1 : ℂ)) ⊗ₜ[ℂ] (j • (1 : ℂ)))) := by simp
    _ = _ := by
      rw [TensorProduct.smul_tmul_smul, TensorProduct.smul_tmul_smul,
        TensorProduct.smul_tmul_smul, map_smul]
      rfl

def scalarCoefficient (hc : ∀ r, (u r 1)^2 * d r 1 * e r 1 = 1) : Residual u d e where
  toLinearMap := (TensorProduct.lift (LinearMap.mul ℂ ℂ)).comp
    (TensorProduct.map (TensorProduct.lift (LinearMap.mul ℂ ℂ))
      (TensorProduct.lift (LinearMap.mul ℂ ℂ)))
  isIntertwining' r := by
    ext
    change (u r 1 * u r 1) * (d r 1 * e r 1) = (1 * 1) * (1 * 1)
    linear_combination hc r

def scalarEquiv (hc : ∀ r, (u r 1)^2 * d r 1 * e r 1 = 1) : Residual u d e ≃ₗ[ℂ] ℂ where
  toFun f := f (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))
  invFun z := z • scalarCoefficient u d e hc
  left_inv f := by
    apply IntertwiningMap.ext
    ext
    change f _ * ((1 * 1) * (1 * 1)) = f _
    simp only [mul_one]
    rfl
  right_inv z := by change z * ((1 * 1) * (1 * 1)) = z; ring
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nonzero_iff_charge_trivial :
    (∃ f : DuueExchange.Sector u d e, f ≠ 0) ↔
    ∀ r, (u r 1)^2 * d r 1 * e r 1 = 1 := by
  rw [DuueResidualCompleteness.exists_nonzero_iff]
  constructor
  · rintro ⟨k, hk⟩ r
    have hn : k (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) ≠ 0 := by
      intro hz
      apply hk
      apply IntertwiningMap.ext
      ext
      exact hz
    have hi := IntertwiningMap.isIntertwining _ _ k r
      (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))
    change k ((u r 1 ⊗ₜ[ℂ] u r 1) ⊗ₜ[ℂ] (d r 1 ⊗ₜ[ℂ] e r 1)) = k _ at hi
    rw [scalar_formula] at hi
    have hc := mul_right_cancel₀ hn (hi.trans (one_mul _).symm)
    calc
      _ = (u r 1 * u r 1) * (d r 1 * e r 1) := by ring
      _ = 1 := hc
  · intro hc
    let a := scalarEquiv u d e hc
    refine ⟨a.symm 1, ?_⟩
    intro hz
    have h := congrArg a hz
    simp at h

def oneGenerationEquiv : DuueExchange.Sector (Representation.trivial ℂ R ℂ)
    (Representation.trivial ℂ R ℂ) (Representation.trivial ℂ R ℂ) ≃ₗ[ℂ] ℂ :=
  (DuueResidualCompleteness.homEquiv _ _ _).trans
    (scalarEquiv _ _ _ (by intro r; norm_num))

theorem oneGeneration_finrank : Module.finrank ℂ
    (DuueExchange.Sector (Representation.trivial ℂ R ℂ)
      (Representation.trivial ℂ R ℂ) (Representation.trivial ℂ R ℂ)) = 1 := by
  rw [oneGenerationEquiv.finrank_eq]
  exact Module.finrank_self ℂ

end
end Physics.DuueScalarFlavor
