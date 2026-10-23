import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows2

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
theorem row24 : (1/1 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 2 3 2 3 = 0 := by
  have he := h (shear 1) (E 0) (E 2) (E 2) (E 0)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-1/1 : ℂ)*he - (-5/4 : ℂ)*(row14 b h hs) - (-1/1 : ℂ)*(row19 b h hs) - (1/4 : ℂ)*(row6 b h hs)


include h hs in
theorem row25 : (5/4 : ℂ)*component b 0 0 1 1 + (1/1 : ℂ)*component b 2 2 3 3 + (1/4 : ℂ)*component b 3 3 1 1 = 0 := by
  have he := h (shear 1) (E 2) (E 2) (E 0) (E 0)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-1/1 : ℂ)*he - (-5/4 : ℂ)*(row17 b h hs) - (-1/1 : ℂ)*(row18 b h hs)


include h hs in
theorem row26 : (1/1 : ℂ)*component b 1 2 0 3 + (1/1 : ℂ)*component b 1 2 3 0 + (1/1 : ℂ)*component b 1 3 0 2 + (1/1 : ℂ)*component b 1 3 2 0 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 1) (E 0) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-4/3 : ℂ)*he - (1/1 : ℂ)*(row11 b h hs) - (1/1 : ℂ)*(row10 b h hs) - (1/2 : ℂ)*(row2 b h hs) - (1/2 : ℂ)*(row3 b h hs)


include h hs in
theorem row27 : (1/1 : ℂ)*component b 1 2 3 0 + (3/4 : ℂ)*component b 1 3 0 2 + (1/1 : ℂ)*component b 1 3 2 0 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 1) (E 0) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (-3/2 : ℂ)*(row11 b h hs) - (-3/4 : ℂ)*(row10 b h hs) - (-3/8 : ℂ)*(row2 b h hs) - (-3/4 : ℂ)*(row3 b h hs) - (-3/2 : ℂ)*(row26 b h hs)


include h hs in
theorem row28 : (1/1 : ℂ)*component b 0 0 0 0 + (4/9 : ℂ)*component b 0 0 2 2 + (1/9 : ℂ)*component b 0 0 3 3 + (16/9 : ℂ)*component b 0 2 0 2 + (16/9 : ℂ)*component b 0 2 2 0 + (-2/9 : ℂ)*component b 0 3 0 3 + (-2/9 : ℂ)*component b 0 3 3 0 + (4/3 : ℂ)*component b 2 2 0 0 + (16/27 : ℂ)*component b 2 2 2 2 + (4/27 : ℂ)*component b 2 2 3 3 + (-1/3 : ℂ)*component b 3 3 0 0 + (-4/27 : ℂ)*component b 3 3 2 2 + (-1/27 : ℂ)*component b 3 3 3 3 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 0) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (16/27 : ℂ)*he


include h hs in
theorem row29 : (1/1 : ℂ)*component b 0 0 3 3 + (4/1 : ℂ)*component b 0 2 0 2 + (-2/1 : ℂ)*component b 0 3 0 3 + (4/3 : ℂ)*component b 2 2 2 2 + (4/3 : ℂ)*component b 2 2 3 3 + (-4/3 : ℂ)*component b 3 3 2 2 + (-1/3 : ℂ)*component b 3 3 3 3 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 0) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (4/1 : ℂ)*he - (9/2 : ℂ)*(row28 b h hs) - (1/1 : ℂ)*(row12 b h hs)


include h hs in
theorem row30 : (1/1 : ℂ)*component b 0 3 0 3 + (-1/1 : ℂ)*component b 2 2 2 2 + (3/1 : ℂ)*component b 2 3 3 2 + (1/1 : ℂ)*component b 3 3 2 2 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 0) (E 3)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-1/1 : ℂ)*he - (-9/16 : ℂ)*(row28 b h hs) - (-1/2 : ℂ)*(row12 b h hs) - (1/4 : ℂ)*(row29 b h hs) - (-3/1 : ℂ)*(row13 b h hs)


include h hs in
theorem row31 : (1/1 : ℂ)*component b 0 3 3 0 + (-1/1 : ℂ)*component b 2 2 2 2 + (2/1 : ℂ)*component b 2 3 2 3 + (1/1 : ℂ)*component b 2 3 3 2 + (1/1 : ℂ)*component b 3 3 2 2 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 2) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-2/1 : ℂ)*he - (-9/4 : ℂ)*(row28 b h hs) - (-1/2 : ℂ)*(row12 b h hs) - (-1/2 : ℂ)*(row29 b h hs) - (2/1 : ℂ)*(row13 b h hs) - (-2/1 : ℂ)*(row14 b h hs) - (-1/1 : ℂ)*(row30 b h hs)

end
end Physics.LorentzRankFour
