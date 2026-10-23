import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourReduction

/-! Whole colored source control by first-derivative scalar contractions.
No internal-invariant or candidate-span premise is used for source coverage. -/
namespace Physics.HiggsQuarticFourLorentzUpper
set_option autoImplicit false
noncomputable section
open Math ColoredQuarticWords
open DerivativeLiteratureHiggs (Label box seeds)
abbrev A := DerivativeLiteratureHiggs.A
abbrev D := DerivativeLiteratureHiggs.D
abbrev eta := LorentzRankFour.eta
abbrev J := DifferentialEquation.ideal D (seeds 0 0)
def W (s : Label) : A := box (field s)

theorem dirD_mem (u : Dir) {p : A} (hp : p ∈ J) : dirD u p ∈ J := by
  rw [dirD_apply]
  exact (J.restrictScalars ℂ).sum_mem (fun i _ => (J.restrictScalars ℂ).smul_mem _
    (DifferentialEquation.stable D (seeds 0 0) i hp))

theorem double_commute (u v : Dir) (p : A) :
    dirD u (dirD u (dirD v p)) = dirD v (dirD u (dirD u p)) := by
  rw [dirD_commute u v p,dirD_commute u v (dirD u p)]

theorem trace_j2 (s : Label) : (∑ i : Fin 4, eta i • j2 s (E i) (E i)) = W s := by
  simp [j2,j1,E,eta,LorentzRankFour.eta,W,box,Fin.sum_univ_succ]
  abel
theorem trace_j3 (s : Label) (u : Dir) :
    (∑ i : Fin 4, eta i • j3 s (E i) (E i) u) = dirD u (W s) := by
  simp only [j3,j2,j1,double_commute]
  change (∑ i : Fin 4, eta i • dirD u (j2 s (E i) (E i))) = dirD u (W s)
  rw [← trace_j2,map_sum]
  simp only [Derivation.map_smul]
theorem trace_j4 (s : Label) (u v : Dir) :
    (∑ i : Fin 4, eta i • j4 s (E i) (E i) u v) = dirD u (dirD v (W s)) := by
  simp only [j4,j3,j2,j1,double_commute]
  change (∑ i : Fin 4, eta i • dirD u (dirD v (j2 s (E i) (E i)))) = _
  rw [← trace_j2,map_sum]
  simp only [map_sum,Derivation.map_smul]

theorem trace_word_mem (a : Fin 4 → Label) (r : Fin 4) :
    (∑ i : Fin 4, eta i • word a r.castSucc (E i) (E i) (E 0) (E 0)) ∈ J := by
  have hw (s : Label) : W s ∈ J := HiggsQuarticFourReduction.wave_mem s
  fin_cases r
  · change (∑ i : Fin 4, eta i • word a 0 (E i) (E i) (E 0) (E 0)) ∈ J
    have he : (∑ i : Fin 4, eta i • word a 0 (E i) (E i) (E 0) (E 0)) =
        field (a 0)*field (a 1)*field (a 2)*dirD (E 0) (dirD (E 0) (W (a 3))) := by
      rw [← trace_j4]
      simp only [word,Finset.mul_sum,mul_smul_comm]
    rw [he]
    exact J.mul_mem_left _ (dirD_mem _ (dirD_mem _ (hw _)))
  · change (∑ i : Fin 4, eta i • word a 1 (E i) (E i) (E 0) (E 0)) ∈ J
    have he : (∑ i : Fin 4, eta i • word a 1 (E i) (E i) (E 0) (E 0)) =
        field (a 0)*field (a 1)*dirD (E 0) (W (a 2))*j1 (a 3) (E 0) := by
      rw [← trace_j3]
      simp only [word,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
    rw [he]
    exact J.mul_mem_right _ (J.mul_mem_left _ (dirD_mem _ (hw _)))
  · change (∑ i : Fin 4, eta i • word a 2 (E i) (E i) (E 0) (E 0)) ∈ J
    have he : (∑ i : Fin 4, eta i • word a 2 (E i) (E i) (E 0) (E 0)) =
        field (a 0)*field (a 1)*W (a 2)*j2 (a 3) (E 0) (E 0) := by
      rw [← trace_j2]
      simp only [word,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
    rw [he]
    exact J.mul_mem_right _ (J.mul_mem_left _ (hw _))
  · change (∑ i : Fin 4, eta i • word a 3 (E i) (E i) (E 0) (E 0)) ∈ J
    have he : (∑ i : Fin 4, eta i • word a 3 (E i) (E i) (E 0) (E 0)) =
        field (a 0)*W (a 1)*j1 (a 2) (E 0)*j1 (a 3) (E 0) := by
      rw [← trace_j2]
      simp only [word,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
    rw [he]
    exact J.mul_mem_right _ (J.mul_mem_right _ (J.mul_mem_left _ (hw _)))

theorem first_ibp (a : Fin 4 → Label) (u v w x : Dir) :
    dirD u (field (a 0)*j1 (a 1) v*j1 (a 2) w*j1 (a 3) x) =
      word a 4 u v w x+word a 3 u v w x+
        word ![a 0,a 2,a 1,a 3] 3 u w v x+word ![a 0,a 3,a 1,a 2] 3 u x v w := by
  change dirD u (field (a 0)*j1 (a 1) v*j1 (a 2) w*j1 (a 3) x) =
    dirD u (field (a 0))*j1 (a 1) v*j1 (a 2) w*j1 (a 3) x+
    field (a 0)*dirD u (j1 (a 1) v)*j1 (a 2) w*j1 (a 3) x+
    field (a 0)*dirD u (j1 (a 2) w)*j1 (a 1) v*j1 (a 3) x+
    field (a 0)*dirD u (j1 (a 3) x)*j1 (a 1) v*j1 (a 2) w
  simp only [Derivation.leibniz]
  ring

variable (f : A →ₗ[ℂ] ℂ)
  (hInv : ∀ g p, p ∈ HiggsQuarticFourInput.V → f (HiggsLagrangianInput.transport g p) = f p)
  (hRel : HiggsQuarticFourInput.P.relations ≤ f.ker)
  (hK : ∀ a b c d : Label, f (DerivativeLiteratureHiggs.pair (field a) (field b)*
    DerivativeLiteratureHiggs.pair (field c) (field d)) = 0)

include hRel in
theorem trace_zero (a : Fin 4 → Label) (r : Fin 4) :
    (∑ i : Fin 4, eta i*LorentzRankFour.component (tensor f a r.castSucc) i i 0 0) = 0 := by
  have hz := HiggsQuarticFourReduction.ideal_zero f hRel (trace_word_mem a r)
  simpa only [map_sum,map_smul,smul_eq_mul,LorentzRankFour.component,tensor_apply,
    E,LorentzFiniteControls.E] using hz

include hInv hRel hK in
theorem lower_word_zero (a : Fin 4 → Label) (r : Fin 4) (i j k l : Fin 4) :
    f (word a r.castSucc (E i) (E j) (E k) (E l)) = 0 := by
  have hi := HiggsQuarticFourTensors.tensor_invariant f hInv a r.castSucc
  have hs := HiggsQuarticFourTensors.tensor_symmetric f a r
  have ht := trace_zero f hRel a r
  fin_cases r
  · apply LorentzRankFour.zero_of_trace_and_symmetric _ hi hs ?_ ht i j k l
    simp only [LorentzRankFour.component,tensor_apply]
    change f (word a 0 (E 0) (E 0) (E 1) (E 1)) = f (word a 0 (E 0) (E 1) (E 0) (E 1))
    simp only [word,j4,j3_sym (a 3) (E 0) (E 1)]
  · apply LorentzRankFour.zero_of_trace_and_symmetric _ hi hs ?_ ht i j k l
    simp only [LorentzRankFour.component,tensor_apply]
    change f (word a 1 (E 0) (E 0) (E 1) (E 1)) = f (word a 1 (E 0) (E 1) (E 0) (E 1))
    simp only [word,j3,j2_sym (a 2) (E 0) (E 1)]
  · apply LorentzRankFour.zero_of_trace_and_cross _ hi hs ht ?_ i j k l
    change (∑ i : Fin 4, ∑ j : Fin 4,
      eta i*eta j*f (word a 2 (E i) (E j) (E i) (E j))) = 0
    simpa only [HiggsQuarticFourReduction.B2,word,j2,j1,E,dirD_single,one_smul,
      LorentzRankFour.component,tensor_apply,map_sum,map_smul,smul_eq_mul,
      HiggsQuarticFourTensors.field_eq,eta,HiggsQuarticFourReduction.eta] using
      HiggsQuarticFourReduction.B2_zero f hRel hK (a 0) (a 1) (a 2) (a 3)
  · apply LorentzRankFour.zero_of_trace_and_cross _ hi hs ht ?_ i j k l
    change (∑ i : Fin 4, ∑ j : Fin 4,
      eta i*eta j*f (word a 3 (E i) (E j) (E i) (E j))) = 0
    simpa only [HiggsQuarticFourReduction.C3,word,j2,j1,E,dirD_single,one_smul,
      LorentzRankFour.component,tensor_apply,map_sum,map_smul,smul_eq_mul,
      HiggsQuarticFourTensors.field_eq,eta,HiggsQuarticFourReduction.eta] using
      HiggsQuarticFourReduction.C3_zero f hRel hK (a 0) (a 1) (a 2) (a 3)

include hInv hRel hK in
theorem word_zero (a : Fin 4 → Label) (r : Fin 5) (i j k l : Fin 4) :
    f (word a r (E i) (E j) (E k) (E l)) = 0 := by
  have hz (a : Fin 4 → Label) (r : Fin 4) := lower_word_zero f hInv hRel hK a r
  have h3 (a : Fin 4 → Label) (i j k l : Fin 4) :
      f (word a 3 (E i) (E j) (E k) (E l)) = 0 := hz a 3 i j k l
  fin_cases r
  · exact hz a 0 i j k l
  · exact hz a 1 i j k l
  · exact hz a 2 i j k l
  · exact hz a 3 i j k l
  · have he := congrArg f (first_ibp a (E i) (E j) (E k) (E l))
    have hd : f (dirD (E i) (field (a 0)*j1 (a 1) (E j)*j1 (a 2) (E k)*j1 (a 3) (E l))) = 0 := by
      simpa only [E,dirD_single,one_smul] using HiggsQuarticFourReduction.derivative_zero f hRel i _
    simp only [map_add,hd,h3,add_zero] at he
    exact he.symm

include hInv hRel hK in
theorem whole_grade_zero (p : HiggsQuarticFourInput.V) : f p.val = 0 := by
  have hp : p.val ∈ ColoredQuarticSource.wordSpan Label := by
    rw [← ColoredQuarticSource.grade_eq_span]
    exact p.property
  refine Submodule.span_induction (p := fun p _ => f p = 0) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨a,r,i,j,k,l,rfl⟩
    exact word_zero f hInv hRel hK a r i j k l
  · exact f.map_zero
  · intro p q _ _ hp hq; rw [map_add,hp,hq,add_zero]
  · intro c p _ hp; rw [map_smul,hp,smul_zero]

end
end Physics.HiggsQuarticFourLorentzUpper
