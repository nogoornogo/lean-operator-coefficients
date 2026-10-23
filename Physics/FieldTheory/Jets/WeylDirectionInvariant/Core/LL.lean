import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Basic

/-! Generated sparse certificates, checked against actual group rows. -/
namespace Physics.WeylDirectionInvariant.LL
set_option autoImplicit false
noncomputable section
open Math LorentzDirections LorentzFiniteControls
variable (f : Tensor)
  (h : ∀ g u v w, f (LorentzJetIBP.weyl false g u)
    (LorentzJetIBP.weyl false g v) (direction g w) = f u v w)

include h in
theorem row0 : (1/1 : ℂ)*component f 0 0 0 = 0 := by
  have he := row false false f h 0 0 0 0
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row1 : (1/1 : ℂ)*component f 0 0 3 = 0 := by
  have he := row false false f h 0 0 0 3
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row2 : (1/1 : ℂ)*component f 0 1 1 = 0 := by
  have he := row false false f h 0 0 1 1
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row3 : (1/1 : ℂ)*component f 0 1 2 = 0 := by
  have he := row false false f h 0 0 1 2
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row4 : (1/1 : ℂ)*component f 1 0 1 = 0 := by
  have he := row false false f h 0 1 0 1
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row5 : (1/1 : ℂ)*component f 1 0 2 = 0 := by
  have he := row false false f h 0 1 0 2
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row6 : (1/1 : ℂ)*component f 1 1 0 = 0 := by
  have he := row false false f h 0 1 1 0
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row7 : (1/1 : ℂ)*component f 1 1 3 = 0 := by
  have he := row false false f h 0 1 1 3
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/2 : ℂ)*he

include h in
theorem row8 : (1/1 : ℂ)*component f 0 0 2 = 0 := by
  have he := row false false f h 2 0 1 2
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (1/1 : ℂ)*he

include h in
theorem row9 : (1/1 : ℂ)*component f 0 0 1 = 0 := by
  have he := row false false f h 3 0 1 1
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (1/1 : ℂ)*he

include h in
theorem row10 : (1/1 : ℂ)*component f 1 1 1 = 0 := by
  have he := row false false f h 1 0 0 1
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/1 : ℂ)*he - (1/1 : ℂ)*(row9 f h)

include h in
theorem row11 : (1/1 : ℂ)*component f 1 1 2 = 0 := by
  have he := row false false f h 1 0 0 2
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (1/1 : ℂ)*he - (-1/1 : ℂ)*(row8 f h)

include h in
theorem row12 : (1/1 : ℂ)*component f 0 1 0 + (1/1 : ℂ)*component f 1 0 0 = 0 := by
  have he := row false false f h 1 0 1 0
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/1 : ℂ)*he

include h in
theorem row13 : (1/1 : ℂ)*component f 0 1 3 + (-1/1 : ℂ)*component f 1 0 3 = 0 := by
  have he := row false false f h 1 0 1 3
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (-1/1 : ℂ)*he

include h in
theorem row14 : (1/1 : ℂ)*component f 1 0 0 + (1/1 : ℂ)*component f 1 0 3 = 0 := by
  have he := row false false f h 2 0 1 1
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (1/1 : ℂ)*he - (-1/1 : ℂ)*(row0 f h) - (1/1 : ℂ)*(row9 f h) - (1/1 : ℂ)*(row1 f h) - (-1/1 : ℂ)*(row12 f h) - (1/1 : ℂ)*(row13 f h)

include h in
theorem row15 : (1/1 : ℂ)*component f 1 0 3 = 0 := by
  have he := row false false f h 2 1 0 1
  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,
    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he
  linear_combination (norm := ring_nf) (1/2 : ℂ)*he - (-1/2 : ℂ)*(row0 f h) - (1/2 : ℂ)*(row9 f h) - (1/2 : ℂ)*(row1 f h) - (-1/2 : ℂ)*(row14 f h)

include h in
theorem value113 : component f 1 1 3 = 0 := by
  have he := row7 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value112 : component f 1 1 2 = 0 := by
  have he := row11 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value111 : component f 1 1 1 = 0 := by
  have he := row10 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value110 : component f 1 1 0 = 0 := by
  have he := row6 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value103 : component f 1 0 3 = 0 := by
  have he := row15 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value102 : component f 1 0 2 = 0 := by
  have he := row5 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value101 : component f 1 0 1 = 0 := by
  have he := row4 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value100 : component f 1 0 0 = 0 := by
  have he := row14 f h
  rw [value103 f h] at he
  linear_combination (norm := ring_nf) he

include h in
theorem value013 : component f 0 1 3 = 0 := by
  have he := row13 f h
  rw [value103 f h] at he
  linear_combination (norm := ring_nf) he

include h in
theorem value012 : component f 0 1 2 = 0 := by
  have he := row3 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value011 : component f 0 1 1 = 0 := by
  have he := row2 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value010 : component f 0 1 0 = 0 := by
  have he := row12 f h
  rw [value100 f h] at he
  linear_combination (norm := ring_nf) he

include h in
theorem value003 : component f 0 0 3 = 0 := by
  have he := row1 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value002 : component f 0 0 2 = 0 := by
  have he := row8 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value001 : component f 0 0 1 = 0 := by
  have he := row9 f h
  linear_combination (norm := ring_nf) he

include h in
theorem value000 : component f 0 0 0 = 0 := by
  have he := row0 f h
  linear_combination (norm := ring_nf) he

include h in
theorem components (a b : Fin 2) (i : Fin 4) :
    component f a b i = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases i
  all_goals norm_num [kernel,fromPauli,value113 f h,value112 f h,value111 f h,value110 f h,value103 f h,value102 f h,value101 f h,value100 f h,value013 f h,value012 f h,value011 f h,value010 f h,value003 f h,value002 f h,value001 f h,value000 f h]

end
end Physics.WeylDirectionInvariant.LL
