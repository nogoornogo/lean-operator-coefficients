import Physics.FieldTheory.Jets.LorentzRankFour.Core.Invariant

/-! Three metric pairings give invariant tensors without pair-symmetry premises. -/
namespace Physics.LorentzRankFourThree
set_option autoImplicit false
noncomputable section
open Math LorentzRankFour LorentzDirections LorentzFiniteControls

theorem reconstruct (T : Tensor) (a b c : ℂ)
    (hc : ∀ i j k l : Fin 4, T (E i) (E j) (E k) (E l) =
      a*metric i j*metric k l+b*metric i k*metric j l+c*metric i l*metric j k)
    (u v w x : Dir) : T u v w x = a*metricPair u v*metricPair w x+
      b*metricPair u w*metricPair v x+c*metricPair u x*metricPair v w := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u y hu hy =>
    simp only [map_add,LinearMap.add_apply,hu,hy]
    ring
  | single i z =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v y hv hy =>
      simp only [map_add,LinearMap.add_apply,hv,hy]
      ring
    | single j t =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w y hw hy =>
        simp only [map_add,LinearMap.add_apply,hw,hy]
        ring
      | single k s =>
        induction x using Finsupp.induction_linear with
        | zero => simp
        | add x y hx hy =>
          simp only [map_add,hx,hy]
          ring
        | single l q =>
          have hi : Finsupp.single i z = z • E i := by simp [E]
          have hj : Finsupp.single j t = t • E j := by simp [E]
          have hk : Finsupp.single k s = s • E k := by simp [E]
          have hl : Finsupp.single l q = q • E l := by simp [E]
          simp only [hi,hj,hk,hl,map_smul,LinearMap.smul_apply,smul_eq_mul,metricPair_basis,hc]
          ring

theorem invariant_of_components (T : Tensor) (a b c : ℂ)
    (hc : ∀ i j k l : Fin 4, T (E i) (E j) (E k) (E l) =
      a*metric i j*metric k l+b*metric i k*metric j l+c*metric i l*metric j k)
    (g : Group) (u v w x : Dir) :
    T (direction g u) (direction g v) (direction g w) (direction g x) = T u v w x := by
  rw [reconstruct T a b c hc,reconstruct T a b c hc]
  simp only [metricPair_invariant]

theorem double_trace (T : Tensor) (a b c : ℂ)
    (hc : ∀ i j k l : Fin 4, T (E i) (E j) (E k) (E l) =
      a*metric i j*metric k l+b*metric i k*metric j l+c*metric i l*metric j k) :
    (∑ i : Fin 4, ∑ j : Fin 4, eta i*eta j*T (E i) (E i) (E j) (E j)) = 16*a+4*b+4*c := by
  simp only [hc]
  norm_num [Fin.sum_univ_succ,metric,eta,LorentzRankFour.eta]
  ring

end
end Physics.LorentzRankFourThree
