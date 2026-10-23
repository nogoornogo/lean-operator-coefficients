import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows1

/-! Generated exact certificates; see generate-rank-four-control.py.
Each identity is rechecked by Lean, without imported rank premises. -/
namespace Physics.LorentzRankFour
set_option autoImplicit false
noncomputable section
open Math LorentzFiniteControls LorentzDirections
variable (b : Tensor)
  (h : ∀ g u v w x, b (direction g u) (direction g v)
    (direction g w) (direction g x) = b u v w x)
  (hs : ∀ u v w x, b u v w x = b v u w x)

include h hs in
theorem row16 : (1/1 : ℂ)*component b 1 3 2 0 = 0 := by
  have he := h (shear 1) (E 1) (E 3) (E 2) (E 0)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-4/7 : ℂ)*he - (3/7 : ℂ)*(row11 b h hs) - (3/14 : ℂ)*(row3 b h hs)


include h hs in
theorem row17 : (1/1 : ℂ)*component b 2 2 0 0 + (1/1 : ℂ)*component b 2 2 3 3 = 0 := by
  have he := h (shear 1) (E 2) (E 2) (E 1) (E 1)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he


include h hs in
theorem row18 : (5/4 : ℂ)*component b 0 0 1 1 + (1/1 : ℂ)*component b 2 2 1 1 + (1/4 : ℂ)*component b 3 3 1 1 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 0) (E 1) (E 1)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he


include h hs in
theorem row19 : (5/4 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 1 2 2 1 + (1/4 : ℂ)*component b 1 3 3 1 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 1) (E 0) (E 1)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he


include h hs in
theorem row20 : (1/1 : ℂ)*component b 1 2 1 2 + (-1/1 : ℂ)*component b 1 3 1 3 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 1) (E 1) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (5/4 : ℂ)*(row5 b h hs)


include h hs in
theorem row21 : (1/1 : ℂ)*component b 1 1 2 2 + (-1/1 : ℂ)*component b 1 1 3 3 = 0 := by
  have he := h (shear Complex.I) (E 1) (E 1) (E 0) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (5/4 : ℂ)*(row4 b h hs)


include h hs in
theorem row22 : (1/1 : ℂ)*component b 1 1 3 3 + (-1/1 : ℂ)*component b 3 3 2 2 = 0 := by
  have he := h (shear 1) (E 0) (E 0) (E 2) (E 2)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (5/4 : ℂ)*(row12 b h hs) - (1/1 : ℂ)*(row21 b h hs)


include h hs in
theorem row23 : (1/1 : ℂ)*component b 1 3 1 3 + (-1/1 : ℂ)*component b 2 3 3 2 = 0 := by
  have he := h (shear 1) (E 0) (E 2) (E 0) (E 2)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (5/4 : ℂ)*(row13 b h hs) - (1/1 : ℂ)*(row20 b h hs)

end
end Physics.LorentzRankFour
