import Math.RepresentationTheory.Jets.DerivativeLiteratureLiHiggs
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourReduction

/-! Full-relation, ordinary-derivative dictionary for Li et al., Eq. (4.8).
No invariant global extension or literature count is assumed. -/
namespace Physics.HiggsQuarticFourLiRelations
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs HiggsQuarticFourReduction
open DerivativeLiteratureLiHiggs

variable (f : A →ₗ[ℂ] ℂ) (hRel : HiggsQuarticFourInput.P.relations ≤ f.ker)

theorem pair_comm (a b : A) : pair a b = pair b a := by unfold pair; ring

include hRel in
theorem C3_formula (a b c d : Label) :
    f (C3 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2)) =
      (1/2:ℂ)*(f (pair (h a.1 a.2) (h b.1 b.2)*pair (h c.1 c.2) (h d.1 d.2))-
        f (pair (h a.1 a.2) (h c.1 c.2)*pair (h b.1 b.2) (h d.1 d.2))-
        f (pair (h a.1 a.2) (h d.1 d.2)*pair (h b.1 b.2) (h c.1 c.2))) := by
  have h1 := C3_relation f hRel a b c d
  have h2 := C3_relation f hRel a c b d
  have h3 := C3_relation f hRel a b d c
  rw [C3_swap (h a.1 a.2) (h c.1 c.2) (h b.1 b.2) (h d.1 d.2),
    C3_swap (h a.1 a.2) (h d.1 d.2) (h b.1 b.2) (h c.1 c.2)] at h2
  rw [C3_swap (h a.1 a.2) (h b.1 b.2) (h d.1 d.2) (h c.1 c.2)] at h3
  linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*h2+(1/2:ℂ)*h3

theorem pair_box_mem (c d : Label) :
    pair (h c.1 c.2) (box (h d.1 d.2)) ∈ DifferentialEquation.ideal D (seeds 0 0) := by
  unfold pair
  have hd i := DifferentialEquation.stable D (seeds 0 0) i (wave_mem d)
  exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _
    (Ideal.mul_mem_left _ _ (hd 0)) (Ideal.mul_mem_left _ _ (hd 1)))
    (Ideal.mul_mem_left _ _ (hd 2))) (Ideal.mul_mem_left _ _ (hd 3))

include hRel in
theorem B2_formula (a b c d : Label) :
    f (B2 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2)) =
      f (pair (h a.1 a.2) (h b.1 b.2)*pair (h c.1 c.2) (h d.1 d.2)) := by
  have hz := congrArg f (divergence2 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2))
  have he : f (h a.1 a.2*h b.1 b.2*pair (h c.1 c.2) (box (h d.1 d.2))) = 0 :=
    ideal_zero f hRel (Ideal.mul_mem_left _ _ (pair_box_mem c d))
  simp only [map_sum,derivative_zero f hRel,Finset.sum_const_zero,map_add,he,add_zero,
    C3_formula f hRel] at hz
  have p1 := pair_comm (h d.1 d.2) (h a.1 a.2)
  have p2 := pair_comm (h d.1 d.2) (h b.1 b.2)
  have p3 := pair_comm (h d.1 d.2) (h c.1 c.2)
  have p4 := pair_comm (h b.1 b.2) (h a.1 a.2)
  simp only [p1,p2,p3,p4] at hz
  have hm (p q : A) : f (p*q) = f (q*p) := congrArg f (mul_comm p q)
  rw [hm (pair (h b.1 b.2) (h d.1 d.2)) (pair (h a.1 a.2) (h c.1 c.2))] at hz
  rw [hm (pair (h b.1 b.2) (h c.1 c.2)) (pair (h a.1 a.2) (h d.1 d.2))] at hz
  linear_combination -hz

theorem box_add (p q : A) : box (p+q) = box p+box q := by simp [box]; abel
theorem box_sub (p q : A) : box (p-q) = box p-box q := by simp [box]; abel
theorem box_commute (i : Fin 4) (p : A) : box (D i p) = D i (box p) := by
  have ht (j : Fin 4) : D j (D j (D i p)) = D i (D j (D j p)) := by
    calc
      _ = D j (D i (D j p)) := congrArg (D j) (ScalarJetAlgebra.totalDerivative_commute j i p)
      _ = _ := ScalarJetAlgebra.totalDerivative_commute j i (D j p)
  simp only [box,map_sub,ht]

theorem adjoint_identity (p q : A) :
    (∑ i : Fin 4, D i (metric i • (p*D i q-D i p*q))) = p*box q-box p*q := by
  simp [Fin.sum_univ_succ,metric,box]
  ring

include hRel in
theorem box_adjoint (p q : A) : f (p*box q) = f (box p*q) := by
  have hz := congrArg f (adjoint_identity p q)
  simp only [map_sum,derivative_zero f hRel,Finset.sum_const_zero,map_sub] at hz
  exact sub_eq_zero.mp hz.symm

theorem box_rho_mem : box rho-2*kinetic ∈ DifferentialEquation.ideal D (seeds 0 0) := by
  rw [box_rho]
  have he : box (h true 0)*h false 0+h true 0*box (h false 0)+
      (box (h true 1)*h false 1+h true 1*box (h false 1))+2*kinetic-2*kinetic =
      box (h true 0)*h false 0+h true 0*box (h false 0)+
      (box (h true 1)*h false 1+h true 1*box (h false 1)) := by ring
  rw [he]
  exact Ideal.add_mem _
    (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (wave_mem (true,0)))
      (Ideal.mul_mem_left _ _ (wave_mem (false,0))))
    (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (wave_mem (true,1)))
      (Ideal.mul_mem_left _ _ (wave_mem (false,1))))

include hRel in
theorem l1_value : f l1 = 4*f q3 := by
  have he : box rho*box rho-4*q3 = (box rho-2*kinetic)*(box rho+2*kinetic) := by
    rw [HiggsQuarticFourInput.q3_pairs]
    simp [Fin.sum_univ_succ,kinetic]
    ring
  have hz := ideal_zero f hRel (show box rho*box rho-4*q3 ∈
      DifferentialEquation.ideal D (seeds 0 0) by
    rw [he]; exact Ideal.mul_mem_right _ _ box_rho_mem)
  have hs : (4:A)*q3 = (4:ℂ) • q3 := by
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_ofNat]
  rw [hs,map_sub,map_smul] at hz
  change f (rho*box (box rho)) = _
  rw [box_adjoint f hRel rho (box rho)]
  exact sub_eq_zero.mp hz

theorem l2_literal : l2 = ∑ a : Fin 2, ∑ b : Fin 2,
    B2 (h true a) (h false b) (h false a) (h true b) := by
  simp [l2,second,secondDual,B2,eta,LorentzRankFour.eta,metric,Fin.sum_univ_succ]
  ring

include hRel in
theorem l2_value : f l2 = f q1 := by
  rw [l2_literal,HiggsQuarticFourInput.q1_pairs]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact (B2_formula f hRel (true,a) (false,b) (false,a) (true,b)).trans
    (congrArg f (congrArg (fun p : A => pair (h true a) (h false b)*p)
      (pair_comm (h false a) (h true b))))

theorem box_left_mem (i : Fin 4) :
    box (leftCurrent i)-2*(pair (h true 0) (D i (h false 0))+
      pair (h true 1) (D i (h false 1))) ∈ DifferentialEquation.ideal D (seeds 0 0) := by
  rw [leftCurrent,box_add,box_product,box_product,box_commute,box_commute]
  have he : box (h true 0)*D i (h false 0)+h true 0*D i (box (h false 0))+
      2*pair (h true 0) (D i (h false 0))+
      (box (h true 1)*D i (h false 1)+h true 1*D i (box (h false 1))+
      2*pair (h true 1) (D i (h false 1)))-
      2*(pair (h true 0) (D i (h false 0))+pair (h true 1) (D i (h false 1))) =
      box (h true 0)*D i (h false 0)+h true 0*D i (box (h false 0))+
      (box (h true 1)*D i (h false 1)+h true 1*D i (box (h false 1))) := by ring
  rw [he]
  exact Ideal.add_mem _
    (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (wave_mem (true,0)))
      (Ideal.mul_mem_left _ _ (DifferentialEquation.stable D _ i (wave_mem (false,0)))))
    (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (wave_mem (true,1)))
      (Ideal.mul_mem_left _ _ (DifferentialEquation.stable D _ i (wave_mem (false,1)))))

def reduced3 : A := ∑ a : Fin 2, ∑ b : Fin 2,
  C3 (h false b) (h false a) (h true a) (h true b)

theorem l3_remainder : l3-2*reduced3 = ∑ i : Fin 4,
    metric i • (rightCurrent i*(box (leftCurrent i)-
      2*(pair (h true 0) (D i (h false 0))+pair (h true 1) (D i (h false 1))))) := by
  have h10 (p : A) := ScalarJetAlgebra.totalDerivative_commute 1 0 p
  have h20 (p : A) := ScalarJetAlgebra.totalDerivative_commute 2 0 p
  have h21 (p : A) := ScalarJetAlgebra.totalDerivative_commute 2 1 p
  have h30 (p : A) := ScalarJetAlgebra.totalDerivative_commute 3 0 p
  have h31 (p : A) := ScalarJetAlgebra.totalDerivative_commute 3 1 p
  have h32 (p : A) := ScalarJetAlgebra.totalDerivative_commute 3 2 p
  simp [l3,reduced3,C3,pair,rightCurrent,eta,LorentzRankFour.eta,metric,Fin.sum_univ_succ]
  simp only [h10,h20,h21,h30,h31,h32]
  ring

include hRel in
theorem l3_value : f l3 = f q2-f q1-f q3 := by
  have hz := ideal_zero f hRel (show l3-2*reduced3 ∈ DifferentialEquation.ideal D (seeds 0 0) by
    rw [l3_remainder]
    apply Submodule.sum_mem
    intro i _
    simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using
      Ideal.mul_mem_left (DifferentialEquation.ideal D (seeds 0 0)) (C (metric i))
        (Ideal.mul_mem_left _ _ (box_left_mem i)))
  have hs : (2:A)*reduced3 = (2:ℂ) • reduced3 := by
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_ofNat]
  rw [hs,map_sub,map_smul] at hz
  have hc (a b : Fin 2) := C3_formula f hRel (false,b) (false,a) (true,a) (true,b)
  simp only [reduced3,map_sum,hc] at hz
  rw [HiggsQuarticFourInput.q1_pairs,HiggsQuarticFourInput.q2_pairs,
    HiggsQuarticFourInput.q3_pairs]
  simp only [Fin.sum_univ_two,map_add] at hz ⊢
  have hq : (pair (h true 0) (h false 0)+pair (h true 1) (h false 1))^2 =
      pair (h true 0) (h false 0)*pair (h true 0) (h false 0)+
      2 • (pair (h true 0) (h false 0)*pair (h true 1) (h false 1))+
      pair (h true 1) (h false 1)*pair (h true 1) (h false 1) := by
    simp only [two_smul]; ring
  rw [hq,map_add,map_add,map_nsmul]
  have hp (a b : Fin 2) := pair_comm (h false a) (h true b)
  simp only [hp] at hz
  have hm (p q : A) : f (p*q) = f (q*p) := congrArg f (mul_comm p q)
  rw [pair_comm (h true 1) (h true 0),pair_comm (h false 1) (h false 0)] at hz ⊢
  simp only [hm,smul_eq_mul,nsmul_eq_mul] at hz ⊢
  linear_combination hz

end
end Physics.HiggsQuarticFourLiRelations
