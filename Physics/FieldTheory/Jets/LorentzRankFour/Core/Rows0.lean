import Physics.FieldTheory.Jets.LorentzRankFour.Core.Basic

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
theorem row0 : (1/1 : ℂ)*component b 0 2 3 1 + (-1/2 : ℂ)*component b 0 3 2 1 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 0) (E 1)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-1/1 : ℂ)*he


include h hs in
theorem row1 : (1/1 : ℂ)*component b 0 2 1 3 + (-1/2 : ℂ)*component b 0 3 1 2 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 1) (E 0)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-1/1 : ℂ)*he


include h hs in
theorem row2 : (1/1 : ℂ)*component b 0 3 1 2 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 1) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-2/3 : ℂ)*he - (4/3 : ℂ)*(row1 b h hs)


include h hs in
theorem row3 : (1/1 : ℂ)*component b 0 3 2 1 = 0 := by
  have he := h (shear Complex.I) (E 0) (E 3) (E 2) (E 1)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (-2/3 : ℂ)*he - (4/3 : ℂ)*(row0 b h hs)


include h hs in
theorem row4 : (1/1 : ℂ)*component b 1 1 0 0 + (1/1 : ℂ)*component b 1 1 3 3 = 0 := by
  have he := h (shear Complex.I) (E 1) (E 1) (E 2) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he


include h hs in
theorem row5 : (1/1 : ℂ)*component b 0 1 1 0 + (1/1 : ℂ)*component b 1 3 1 3 = 0 := by
  have he := h (shear Complex.I) (E 1) (E 2) (E 1) (E 2)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he


include h hs in
theorem row6 : (1/1 : ℂ)*component b 0 1 0 1 + (1/1 : ℂ)*component b 1 3 3 1 = 0 := by
  have he := h (shear Complex.I) (E 1) (E 2) (E 2) (E 1)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he


include h hs in
theorem row7 : (1/1 : ℂ)*component b 0 0 1 1 + (1/1 : ℂ)*component b 3 3 1 1 = 0 := by
  have he := h (shear Complex.I) (E 2) (E 2) (E 1) (E 1)
  simp only [imag_basis,map_sum,LinearMap.sum_apply,map_smul,
    LinearMap.smul_apply,smul_eq_mul] at he
  norm_num [Fin.sum_univ_succ,imagRows] at he
  simp only [← component_apply] at he
  simp only [normalize b h hs] at he
  norm_num [normalComponent,killed,signsZ,signsX,← component_apply] at he
  linear_combination (1/1 : ℂ)*he

end
end Physics.LorentzRankFour
