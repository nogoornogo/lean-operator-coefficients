import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows3

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
theorem row32 : (1/1 : ℂ)*component b 2 2 2 2 + (-2/1 : ℂ)*component b 2 3 3 2 + (-1/1 : ℂ)*component b 3 3 2 2 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 2) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (3/1 : ℂ)*he - (9/4 : ℂ)*(row28 b h hs) - (5/4 : ℂ)*(row12 b h hs) - (2/1 : ℂ)*(row29 b h hs) - (-6/1 : ℂ)*(row13 b h hs) - (2/1 : ℂ)*(row14 b h hs) - (3/1 : ℂ)*(row30 b h hs) - (-1/1 : ℂ)*(row31 b h hs)


include h hs in
theorem row33 : (1/1 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 2 3 3 2 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 3) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (9/16 : ℂ)*(row28 b h hs) - (1/2 : ℂ)*(row12 b h hs) - (-1/4 : ℂ)*(row29 b h hs) - (1/1 : ℂ)*(row13 b h hs) - (2/1 : ℂ)*(row14 b h hs) - (-1/2 : ℂ)*(row30 b h hs) - (-1/2 : ℂ)*(row31 b h hs) - (-1/1 : ℂ)*(row24 b h hs)


include h hs in
theorem row34 : (-10/9 : ℂ)*component b 0 0 1 1 + (2/9 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 3 3 0 0 + (-2/9 : ℂ)*component b 3 3 1 1 + (1/9 : ℂ)*component b 3 3 3 3 = 0 := by
  have he := h (shear Complex.I) (E 2) (E 3) (E 0) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-4/3 : ℂ)*he - (-3/2 : ℂ)*(row28 b h hs) - (-1/3 : ℂ)*(row13 b h hs) - (-1/3 : ℂ)*(row14 b h hs) - (-1/3 : ℂ)*(row30 b h hs) - (-1/3 : ℂ)*(row31 b h hs) - (-1/1 : ℂ)*(row17 b h hs) - (-10/9 : ℂ)*(row32 b h hs) - (8/9 : ℂ)*(row25 b h hs) - (2/3 : ℂ)*(row24 b h hs) - (-8/9 : ℂ)*(row33 b h hs)


include h hs in
theorem row35 : (1/1 : ℂ)*component b 0 0 1 1 + (2/1 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 3 3 3 3 = 0 := by
  have he := h (shear Complex.I) (E 2) (E 3) (E 0) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-9/1 : ℂ)*he - (-27/4 : ℂ)*(row28 b h hs) - (-3/2 : ℂ)*(row12 b h hs) - (-3/2 : ℂ)*(row29 b h hs) - (-9/4 : ℂ)*(row13 b h hs) - (-3/2 : ℂ)*(row14 b h hs) - (-9/2 : ℂ)*(row30 b h hs) - (-3/2 : ℂ)*(row31 b h hs) - (-9/2 : ℂ)*(row17 b h hs) - (-9/1 : ℂ)*(row32 b h hs) - (3/1 : ℂ)*(row25 b h hs) - (-3/1 : ℂ)*(row33 b h hs) - (9/2 : ℂ)*(row34 b h hs) - (1/4 : ℂ)*(row7 b h hs)


include h hs in
theorem row36 : (3/4 : ℂ)*component b 0 0 1 1 + (3/1 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 1 1 1 1 + (-2/1 : ℂ)*component b 1 1 3 3 + (-3/1 : ℂ)*component b 1 3 1 3 + (-9/4 : ℂ)*component b 2 2 0 0 + (-1/1 : ℂ)*component b 2 2 2 2 + (-1/4 : ℂ)*component b 2 2 3 3 + (3/1 : ℂ)*component b 2 3 2 3 + (3/1 : ℂ)*component b 2 3 3 2 + (-1/4 : ℂ)*component b 3 3 1 1 + (1/1 : ℂ)*component b 3 3 2 2 = 0 := by
  have he := h (shear 1) (E 0) (E 3) (E 0) (E 0)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he - (27/16 : ℂ)*(row28 b h hs) - (-3/4 : ℂ)*(row12 b h hs) - (3/1 : ℂ)*(row5 b h hs) - (-3/1 : ℂ)*(row13 b h hs) - (-3/1 : ℂ)*(row14 b h hs) - (9/4 : ℂ)*(row4 b h hs)


include h hs in
theorem row37 : (1/1 : ℂ)*component b 0 0 1 1 + (1/1 : ℂ)*component b 3 3 2 2 = 0 := by
  have he := h (shear 1) (E 0) (E 3) (E 0) (E 1)
  simp only [real_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,realRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-1/1 : ℂ)*he - (9/8 : ℂ)*(row28 b h hs) - (-1/2 : ℂ)*(row12 b h hs) - (1/4 : ℂ)*(row29 b h hs) - (2/1 : ℂ)*(row5 b h hs) - (-3/1 : ℂ)*(row13 b h hs) - (-2/1 : ℂ)*(row14 b h hs) - (3/2 : ℂ)*(row4 b h hs) - (1/1 : ℂ)*(row36 b h hs) - (1/1 : ℂ)*(row22 b h hs) - (1/1 : ℂ)*(row23 b h hs) - (3/4 : ℂ)*(row17 b h hs) - (-1/1 : ℂ)*(row25 b h hs) - (-1/1 : ℂ)*(row24 b h hs) - (1/1 : ℂ)*(row33 b h hs) - (1/4 : ℂ)*(row7 b h hs)

end
end Physics.LorentzRankFour
