import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Basic

/-! Generated sparse certificates; Lean checks every actual-group identity. -/
namespace Physics.HiggsFirstInternal
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls
attribute [local simp] mul_add add_mul sub_mul mul_sub smul_mul_assoc mul_smul_comm smul_smul smul_eq_mul
variable (f : A →ₗ[ℂ] ℂ)
  (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l))


include hI in
theorem row0 : (-17/9 : ℂ)*K f 0 0 2 2 + (1/1 : ℂ)*K f 0 1 2 3 + (1/1 : ℂ)*K f 1 0 2 3 + (8/9 : ℂ)*K f 1 1 3 3 = 0 := by
  have he := rotation_value f hI 0 0 2 2
  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he
  simp only [← K_apply,normal_form f hI] at he
  norm_num [normalK,ordered,weight] at he
  linear_combination (625/288 : ℂ)*he

include hI in
theorem row1 : (-1/1 : ℂ)*K f 0 0 2 2 + (1/1 : ℂ)*K f 1 1 3 3 = 0 := by
  have he := rotation_value f hI 0 0 2 3
  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he
  simp only [← K_apply,normal_form f hI] at he
  norm_num [normalK,ordered,weight] at he
  linear_combination (-75/32 : ℂ)*he - (-63/200 : ℂ)*(row0 f hI)

include hI in
theorem row2 : (-1/2 : ℂ)*K f 0 0 2 2 + (1/1 : ℂ)*K f 1 0 2 3 = 0 := by
  have he := rotation_value f hI 0 1 2 2
  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he
  simp only [← K_apply,normal_form f hI] at he
  norm_num [normalK,ordered,weight] at he
  linear_combination (25/24 : ℂ)*he - (-9/25 : ℂ)*(row0 f hI)

include hI in
theorem row3 : (-17/9 : ℂ)*K f 2 0 0 2 + (1/1 : ℂ)*K f 2 0 1 3 + (1/1 : ℂ)*K f 3 0 1 2 + (8/9 : ℂ)*K f 3 1 1 3 = 0 := by
  have he := rotation_value f hI 2 0 0 2
  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he
  simp only [← K_apply,normal_form f hI] at he
  norm_num [normalK,ordered,weight] at he
  linear_combination (625/288 : ℂ)*he

include hI in
theorem row4 : (-1/2 : ℂ)*K f 2 0 0 2 + (1/1 : ℂ)*K f 3 0 1 2 = 0 := by
  have he := rotation_value f hI 2 0 0 3
  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he
  simp only [← K_apply,normal_form f hI] at he
  norm_num [normalK,ordered,weight] at he
  linear_combination (25/24 : ℂ)*he - (-9/25 : ℂ)*(row3 f hI)

include hI in
theorem row5 : (-1/1 : ℂ)*K f 2 0 0 2 + (1/1 : ℂ)*K f 3 1 1 3 = 0 := by
  have he := rotation_value f hI 2 0 1 2
  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he
  simp only [← K_apply,normal_form f hI] at he
  norm_num [normalK,ordered,weight] at he
  linear_combination (-75/32 : ℂ)*he - (-63/200 : ℂ)*(row3 f hI)

include hI in
theorem value3113 : K f 3 1 1 3 = (1/1 : ℂ)*K f 2 0 0 2 := by
  have he := row5 f hI
  linear_combination he

include hI in
theorem value3012 : K f 3 0 1 2 = (1/2 : ℂ)*K f 2 0 0 2 := by
  have he := row4 f hI
  linear_combination he

include hI in
theorem value2013 : K f 2 0 1 3 = (1/2 : ℂ)*K f 2 0 0 2 := by
  have he := row3 f hI
  rw [value3012 f hI,value3113 f hI] at he
  linear_combination he

include hI in
theorem value1133 : K f 1 1 3 3 = (1/1 : ℂ)*K f 0 0 2 2 := by
  have he := row1 f hI
  linear_combination he

include hI in
theorem value1023 : K f 1 0 2 3 = (1/2 : ℂ)*K f 0 0 2 2 := by
  have he := row2 f hI
  linear_combination he

include hI in
theorem value0123 : K f 0 1 2 3 = (1/2 : ℂ)*K f 0 0 2 2 := by
  have he := row0 f hI
  rw [value1023 f hI,value1133 f hI] at he
  linear_combination he

end
end Physics.HiggsFirstInternal
