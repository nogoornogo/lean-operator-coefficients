import Physics.FieldTheory.Jets.Lorentz.LorentzRankFour

/-! Trace and metric contractions of the complete pair-symmetric controls. -/
namespace Physics.LorentzRankFour
set_option autoImplicit false
noncomputable section
open Math LorentzFiniteControls LorentzDirections
abbrev eta : Fin 4 → ℂ := ![1,-1,-1,-1]
variable (b : Tensor)
  (h : ∀ g u v w x, b (direction g u) (direction g v)
    (direction g w) (direction g x) = b u v w x)
  (hs : ∀ u v w x, b u v w x = b v u w x)

include h hs in
theorem trace00 : (∑ i : Fin 4, eta i*component b i i 0 0) =
    -4*component b 0 0 1 1-2*component b 0 1 0 1 := by
  have he (i : Fin 4) : eta i*component b i i 0 0 =
      eta i*(-component b 0 0 1 1*(metric i i*metric 0 0)-
        component b 0 1 0 1*(metric i 0*metric i 0+metric i 0*metric i 0)) :=
    congrArg (fun z => eta i*z) (components b h hs i i 0 0)
  simp only [he]
  norm_num [Fin.sum_univ_succ,metric,eta]
  ring

include h hs in
theorem doubleTrace : (∑ i : Fin 4, ∑ j : Fin 4, eta i*eta j*component b i i j j) =
    -16*component b 0 0 1 1-8*component b 0 1 0 1 := by
  have he (i j : Fin 4) : eta i*eta j*component b i i j j =
      eta i*eta j*(-component b 0 0 1 1*(metric i i*metric j j)-
        component b 0 1 0 1*(metric i j*metric i j+metric i j*metric i j)) :=
    congrArg (fun z => eta i*eta j*z) (components b h hs i i j j)
  simp only [he]
  norm_num [Fin.sum_univ_succ,metric,eta]
  ring

include h hs in
theorem crossTrace : (∑ i : Fin 4, ∑ j : Fin 4, eta i*eta j*component b i j i j) =
    -4*component b 0 0 1 1-20*component b 0 1 0 1 := by
  have he (i j : Fin 4) : eta i*eta j*component b i j i j =
      eta i*eta j*(-component b 0 0 1 1*(metric i j*metric i j)-
        component b 0 1 0 1*(metric i i*metric j j+metric i j*metric j i)) :=
    congrArg (fun z => eta i*eta j*z) (components b h hs i j i j)
  simp only [he]
  norm_num [Fin.sum_univ_succ,metric,eta]
  ring

include h hs in
theorem zero_of_trace_and_cross
    (ht : (∑ i : Fin 4, eta i*component b i i 0 0) = 0)
    (hc : (∑ i : Fin 4, ∑ j : Fin 4, eta i*eta j*component b i j i j) = 0)
    (i j k l : Fin 4) : component b i j k l = 0 := by
  rw [trace00 b h hs] at ht
  rw [crossTrace b h hs] at hc
  have ha : component b 0 0 1 1 = 0 := by linear_combination (-5/18 : ℂ)*ht+(1/36 : ℂ)*hc
  have hb : component b 0 1 0 1 = 0 := by linear_combination (1/18 : ℂ)*ht+(-1/18 : ℂ)*hc
  rw [components b h hs,ha,hb]
  ring

include h hs in
theorem zero_of_trace_and_symmetric
    (h3 : component b 0 0 1 1 = component b 0 1 0 1)
    (ht : (∑ i : Fin 4, eta i*component b i i 0 0) = 0)
    (i j k l : Fin 4) : component b i j k l = 0 := by
  rw [trace00 b h hs,h3] at ht
  have hb : component b 0 1 0 1 = 0 := by linear_combination (-1/6 : ℂ)*ht
  rw [components b h hs,h3,hb]
  ring

include h hs in
theorem zero_of_double_trace_and_symmetric
    (h3 : component b 0 0 1 1 = component b 0 1 0 1)
    (ht : (∑ i : Fin 4, ∑ j : Fin 4, eta i*eta j*component b i i j j) = 0)
    (i j k l : Fin 4) : component b i j k l = 0 := by
  rw [doubleTrace b h hs,h3] at ht
  have hb : component b 0 1 0 1 = 0 := by linear_combination (-1/24 : ℂ)*ht
  rw [components b h hs,h3,hb]
  ring

end
end Physics.LorentzRankFour
