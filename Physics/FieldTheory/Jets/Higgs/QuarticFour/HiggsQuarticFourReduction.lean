import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourTensors
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourWaves

/-! Explicit linear IBP reductions of colored metric contractions. -/
namespace Physics.HiggsQuarticFourReduction
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs
abbrev eta := LorentzRankFour.eta

def C3 (a b c d : A) : A :=
  ∑ i : Fin 4, ∑ j : Fin 4, (eta i*eta j) • (a*D i (D j b)*D i c*D j d)
def B2 (a b c d : A) : A :=
  ∑ i : Fin 4, ∑ j : Fin 4, (eta i*eta j) • (a*b*D i (D j c)*D i (D j d))
def current3 (a b c d : A) (i : Fin 4) : A :=
  ∑ j : Fin 4, (eta i*eta j) • (a*D j b*D i c*D j d)
def current2 (a b c d : A) (i : Fin 4) : A :=
  ∑ j : Fin 4, (eta i*eta j) • (a*b*D j c*D i (D j d))

theorem C3_swap (a b c d : A) : C3 a b c d = C3 a b d c := by
  unfold C3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [ScalarJetAlgebra.totalDerivative_commute j i b,mul_comm (eta j) (eta i)]
  apply congrArg (fun p : A => (eta i*eta j) • p)
  ring

theorem divergence3 (a b c d : A) :
    (∑ i : Fin 4, D i (current3 a b c d i)) =
      pair a c*pair b d+C3 a b c d+C3 a d c b+a*box c*pair b d := by
  simp only [current3,C3,map_sum,Derivation.map_smul,ScalarJetAlgebra.totalDerivative_mul]
  simp [Fin.sum_univ_succ,eta,LorentzRankFour.eta,pair,box]
  ring

theorem divergence2 (a b c d : A) :
    (∑ i : Fin 4, D i (current2 a b c d i)) =
      B2 a b c d+C3 a d b c+C3 b d a c+
        a*b*pair c (box d) := by
  have h10 (p : A) := ScalarJetAlgebra.totalDerivative_commute 1 0 p
  have h20 (p : A) := ScalarJetAlgebra.totalDerivative_commute 2 0 p
  have h21 (p : A) := ScalarJetAlgebra.totalDerivative_commute 2 1 p
  have h30 (p : A) := ScalarJetAlgebra.totalDerivative_commute 3 0 p
  have h31 (p : A) := ScalarJetAlgebra.totalDerivative_commute 3 1 p
  have h32 (p : A) := ScalarJetAlgebra.totalDerivative_commute 3 2 p
  simp only [current2,B2,C3,map_sum,Derivation.map_smul,ScalarJetAlgebra.totalDerivative_mul]
  simp [Fin.sum_univ_succ,eta,LorentzRankFour.eta,pair,box]
  simp only [h10,h20,h21,h30,h31,h32]
  ring

variable (f : A →ₗ[ℂ] ℂ) (hRel : HiggsQuarticFourInput.P.relations ≤ f.ker)

include hRel in
theorem derivative_zero (i : Fin 4) (p : A) : f (D i p) = 0 := by
  apply hRel
  rw [HiggsQuarticFourWaves.relations_eq]
  exact Submodule.mem_sup_right ⟨Finsupp.single i p,by
    rw [DifferentialEquation.divergence_single]⟩

include hRel in
theorem ideal_zero {p : A} (hp : p ∈ DifferentialEquation.ideal D (seeds 0 0)) : f p = 0 := by
  apply hRel
  rw [HiggsQuarticFourWaves.relations_eq]
  exact Submodule.mem_sup_left hp

theorem wave_mem (s : Label) : box (h s.1 s.2) ∈ DifferentialEquation.ideal D (seeds 0 0) := by
  simpa [seed] using DifferentialEquation.seed_mem D (seeds 0 0) ⟨s,rfl⟩

include hRel in
theorem C3_relation (a b c d : Label) :
    f (C3 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2))+
      f (C3 (h a.1 a.2) (h d.1 d.2) (h c.1 c.2) (h b.1 b.2)) =
        -f (pair (h a.1 a.2) (h c.1 c.2)*pair (h b.1 b.2) (h d.1 d.2)) := by
  have hz := congrArg f (divergence3 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2))
  have he : f (h a.1 a.2*box (h c.1 c.2)*pair (h b.1 b.2) (h d.1 d.2)) = 0 :=
    ideal_zero f hRel ((DifferentialEquation.ideal D (seeds 0 0)).mul_mem_right _
      ((DifferentialEquation.ideal D (seeds 0 0)).mul_mem_left _ (wave_mem c)))
  simp only [map_sum,derivative_zero f hRel,Finset.sum_const_zero,map_add,he,add_zero] at hz
  linear_combination -hz

include hRel in
theorem C3_zero (hK : ∀ a b c d : Label,
    f (pair (h a.1 a.2) (h b.1 b.2)*pair (h c.1 c.2) (h d.1 d.2)) = 0)
    (a b c d : Label) : f (C3 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2)) = 0 := by
  have h1 := C3_relation f hRel a b c d
  have h2 := C3_relation f hRel a c b d
  have h3 := C3_relation f hRel a b d c
  simp only [hK,neg_zero] at h1 h2 h3
  rw [C3_swap (h a.1 a.2) (h c.1 c.2) (h b.1 b.2) (h d.1 d.2),
    C3_swap (h a.1 a.2) (h d.1 d.2) (h b.1 b.2) (h c.1 c.2)] at h2
  rw [C3_swap (h a.1 a.2) (h b.1 b.2) (h d.1 d.2) (h c.1 c.2)] at h3
  linear_combination (1/2 : ℂ)*h1-(1/2 : ℂ)*h2+(1/2 : ℂ)*h3

include hRel in
theorem B2_zero (hK : ∀ a b c d : Label,
    f (pair (h a.1 a.2) (h b.1 b.2)*pair (h c.1 c.2) (h d.1 d.2)) = 0)
    (a b c d : Label) : f (B2 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2)) = 0 := by
  have hz := congrArg f (divergence2 (h a.1 a.2) (h b.1 b.2) (h c.1 c.2) (h d.1 d.2))
  have he : f (h a.1 a.2*h b.1 b.2*pair (h c.1 c.2) (box (h d.1 d.2))) = 0 := by
    apply ideal_zero f hRel
    apply Ideal.mul_mem_left
    unfold pair
    have hd i := DifferentialEquation.stable D (seeds 0 0) i (wave_mem d)
    exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _
      (Ideal.mul_mem_left _ _ (hd 0)) (Ideal.mul_mem_left _ _ (hd 1)))
      (Ideal.mul_mem_left _ _ (hd 2))) (Ideal.mul_mem_left _ _ (hd 3))
  simp only [map_sum,derivative_zero f hRel,Finset.sum_const_zero,map_add,he,add_zero,
    C3_zero f hRel hK] at hz
  exact hz.symm

end
end Physics.HiggsQuarticFourReduction
