import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExteriorCompleteness
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueScalarFlavor

open Math

/-! One-generation qqql has one coefficient, not four independent local pairings. -/
namespace Physics.QqqlScalarFlavor
set_option autoImplicit false
noncomputable section
open Representation QqqlExchange FourDoubletProductExchange
open scoped TensorProduct
variable {R : Type*} [Group R] (q l : Representation ℂ R ℂ)

def pattern (z : ℂ) (i j : Fin 2) : ℂ := if i = j then 2*z else -z

def family (hc : ∀ r, (q r 1)^2 * q r 1 * l r 1 = 1) (z : ℂ) : Family q l :=
  fun i j => pattern z i j • DuueScalarFlavor.scalarCoefficient q q l hc

theorem family_condition (hc : ∀ r, (q r 1)^2 * q r 1 * l r 1 = 1) (z : ℂ) :
    Condition q l (family q l hc z) := by
  intro x y v h
  have hv (a b c d : ℂ) : values q l (family q l hc z) a b c d =
      fun i j => pattern z i j * ((a*b)*(c*d)) := by
    funext i j
    rfl
  rw [hv, hv, hv]
  constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
    dsimp [exchange01, exchange12, pattern] <;> ring

def residualEquiv (hc : ∀ r, (q r 1)^2 * q r 1 * l r 1 = 1) :
    residualSpace q l ≃ₗ[ℂ] ℂ where
  toFun k := k.val 0 0 (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) / 2
  invFun z := ⟨family q l hc z, family_condition q l hc z⟩
  left_inv k := by
    apply Subtype.ext
    funext i j
    apply IntertwiningMap.ext
    ext
    have h01 := (k.property 1 1 1 1).1
    have h12 := (k.property 1 1 1 1).2
    have h00 := congrFun (congrFun h01 0) 0
    have h10 := congrFun (congrFun h12 1) 0
    have h11 := congrFun (congrFun h12 1) 1
    simp [exchange01, exchange12, values] at h00 h10 h11
    change pattern (k.val 0 0 (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) / 2) i j *
      ((1*1)*(1*1)) = k.val i j (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))
    fin_cases i <;> fin_cases j <;> simp [pattern]
    · ring
    · linear_combination -h00 / 2 - h10 / 2 - h11 / 2
    · linear_combination -h00 / 2 + h10 / 2 - h11 / 2
    · linear_combination h11
  right_inv z := by
    change (2*z * ((1*1)*(1*1))) / 2 = z
    ring
  map_add' k m := add_div _ _ _
  map_smul' z k := mul_div_assoc _ _ _

def oneGenerationEquiv : QqqlExteriorCompleteness.Sector (Representation.trivial ℂ R ℂ)
    (Representation.trivial ℂ R ℂ) ≃ₗ[ℂ] ℂ :=
  (QqqlExteriorCompleteness.exteriorEquiv _ _).trans
    (residualEquiv _ _ (by intro r; norm_num))

theorem oneGeneration_finrank : Module.finrank ℂ
    (QqqlExteriorCompleteness.Sector (Representation.trivial ℂ R ℂ)
      (Representation.trivial ℂ R ℂ)) = 1 := by
  rw [oneGenerationEquiv.finrank_eq]
  exact Module.finrank_self ℂ

end
end Physics.QqqlScalarFlavor
