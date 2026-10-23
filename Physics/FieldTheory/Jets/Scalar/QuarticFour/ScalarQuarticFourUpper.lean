import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourSource
import Physics.FieldTheory.Jets.LorentzRankFour.Core.Contractions

/-! Upper control on the entire quartic order-four invariant coefficient space. -/
namespace Physics.ScalarQuarticFourUpper
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM ScalarQuarticFourTensors
open LorentzFiniteControls ScalarQuarticContractions

theorem double_commute (u v : Dir) (p : OffShell) :
    dirD u (dirD u (dirD v p)) = dirD v (dirD u (dirD u p)) := by
  rw [dirD_commute u v p,dirD_commute u v (dirD u p)]

theorem trace_j2 : (∑ i : Fin 4, eta i • j2 (E i) (E i)) = W := by
  simpa [j2,j1,E] using wave_sum.symm

theorem trace_j3 (u : Dir) : (∑ i : Fin 4, eta i • j3 (E i) (E i) u) = dirD u W := by
  simp only [j3,j2,j1,double_commute]
  change (∑ i : Fin 4, eta i • dirD u (j2 (E i) (E i))) = dirD u W
  rw [← trace_j2,map_sum]
  simp only [Derivation.map_smul]

theorem trace_j4 (u v : Dir) :
    (∑ i : Fin 4, eta i • j4 (E i) (E i) u v) = dirD u (dirD v W) := by
  simp only [j4,j3,j2,j1,double_commute]
  change (∑ i : Fin 4, eta i • dirD u (dirD v (j2 (E i) (E i)))) = dirD u (dirD v W)
  rw [← trace_j2,map_sum]
  simp only [map_sum,Derivation.map_smul]

theorem trace_word0 :
    (∑ i : Fin 4, eta i • word 0 (E i) (E i) (E 0) (E 0)) =
      field^3*dirD (E 0) (dirD (E 0) W) := by
  rw [← trace_j4]
  simp only [word,Finset.mul_sum,mul_smul_comm]

theorem trace_word1 :
    (∑ i : Fin 4, eta i • word 1 (E i) (E i) (E 0) (E 0)) =
      field^2*dirD (E 0) W*j1 (E 0) := by
  rw [← trace_j3]
  simp only [word,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]

theorem trace_word2 :
    (∑ i : Fin 4, eta i • word 2 (E i) (E i) (E 0) (E 0)) =
      field^2*W*j2 (E 0) (E 0) := by
  rw [← trace_j2]
  simp only [word,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]

theorem trace_word3 :
    (∑ i : Fin 4, eta i • word 3 (E i) (E i) (E 0) (E 0)) =
      field*W*j1 (E 0)*j1 (E 0) := by
  rw [← trace_j2]
  simp only [word,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]

theorem trace_word_mem (r : Fin 4) :
    (∑ i : Fin 4, eta i • word r.castSucc (E i) (E i) (E 0) (E 0)) ∈ ideal 0 := by
  have hw := wave_mem
  have hd := DifferentialEquation.stable D (equations 0) 0 hw
  have hdd := DifferentialEquation.stable D (equations 0) 0 hd
  fin_cases r
  · change (∑ i : Fin 4, eta i • word 0 (E i) (E i) (E 0) (E 0)) ∈ ideal 0
    rw [trace_word0]
    simpa [E] using (ideal 0).mul_mem_left (field^3) hdd
  · change (∑ i : Fin 4, eta i • word 1 (E i) (E i) (E 0) (E 0)) ∈ ideal 0
    rw [trace_word1]
    simpa [E] using (ideal 0).mul_mem_right (j1 (E 0)) ((ideal 0).mul_mem_left (field^2) hd)
  · change (∑ i : Fin 4, eta i • word 2 (E i) (E i) (E 0) (E 0)) ∈ ideal 0
    rw [trace_word2]
    exact (ideal 0).mul_mem_right (j2 (E 0) (E 0)) ((ideal 0).mul_mem_left (field^2) hw)
  · change (∑ i : Fin 4, eta i • word 3 (E i) (E i) (E 0) (E 0)) ∈ ideal 0
    rw [trace_word3]
    exact (ideal 0).mul_mem_right (j1 (E 0))
      ((ideal 0).mul_mem_right (j1 (E 0)) ((ideal 0).mul_mem_left field hw))

variable (f : OffShell →ₗ[ℂ] ℂ)
  (hInv : ∀ g p, p ∈ V → f (offAction g p) = f p)
  (hRel : ∀ p, p ∈ P.relations → p ∈ V → f p = 0)

include hRel in
theorem trace_zero (r : Fin 4) :
    (∑ i : Fin 4, LorentzRankFour.eta i*LorentzRankFour.component (tensor f r.castSucc) i i 0 0) = 0 := by
  have hg : (∑ i : Fin 4, eta i • word r.castSucc (E i) (E i) (E 0) (E 0)) ∈ V :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (word_grade _ _ _ _ _))
  have he := hRel _ (Submodule.mem_sup_left (trace_word_mem r)) hg
  simpa only [map_sum,map_smul,smul_eq_mul,LorentzRankFour.component,tensor_apply,
    LorentzRankFour.eta,eta] using he

theorem extra_sym_zero : LorentzRankFour.component (tensor f 0) 0 0 1 1 =
    LorentzRankFour.component (tensor f 0) 0 1 0 1 := by
  change f (field^3*j4 (E 0) (E 0) (E 1) (E 1)) = f (field^3*j4 (E 0) (E 1) (E 0) (E 1))
  simp only [j4,j3,j2,j1]
  rw [dirD_commute (E 0) (E 1) (dirD (E 1) field)]

theorem extra_sym_one : LorentzRankFour.component (tensor f 1) 0 0 1 1 =
    LorentzRankFour.component (tensor f 1) 0 1 0 1 := by
  change f (field^2*j3 (E 0) (E 0) (E 1)*j1 (E 1)) =
    f (field^2*j3 (E 0) (E 1) (E 0)*j1 (E 1))
  simp only [j3,j2,j1]
  rw [dirD_commute (E 0) (E 1) field]

theorem extra_sym_four : LorentzRankFour.component (tensor f 4) 0 0 1 1 =
    LorentzRankFour.component (tensor f 4) 0 1 0 1 := by
  change f (j1 (E 0)*j1 (E 0)*j1 (E 1)*j1 (E 1)) =
    f (j1 (E 0)*j1 (E 1)*j1 (E 0)*j1 (E 1))
  apply congrArg f
  ring

theorem A_word : A = ∑ i : Fin 4, ∑ j : Fin 4,
    (eta i*eta j) • word 2 (E i) (E j) (E i) (E j) := by
  simp [A,word,j2,j1,E,eta,Fin.sum_univ_succ,MvPolynomial.smul_eq_C_mul]
  ring

theorem B_word : B = ∑ i : Fin 4, ∑ j : Fin 4,
    (eta i*eta j) • word 3 (E i) (E j) (E i) (E j) := by
  simp [B,word,j2,j1,E,eta,Fin.sum_univ_succ,MvPolynomial.smul_eq_C_mul]
  ring

theorem C_word : C4 = ∑ i : Fin 4, ∑ j : Fin 4,
    (eta i*eta j) • word 4 (E i) (E i) (E j) (E j) := by
  change K^2 = _
  rw [kinetic_sum]
  simp [word,j1,E,eta,Fin.sum_univ_succ,MvPolynomial.smul_eq_C_mul]
  ring

include hRel in
theorem value_congr {p q : OffShell} (hp : p ∈ V) (hq : q ∈ V)
    (he : ScalarQuarticContractions.q p = ScalarQuarticContractions.q q) : f p = f q := by
  have hr : p-q ∈ P.relations := (Submodule.Quotient.mk_eq_zero _).mp (by
    change ScalarQuarticContractions.q (p-q) = 0
    rw [map_sub,he,sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hRel _ hr (V.sub_mem hp hq))

theorem A_grade : A ∈ V := candidate_grade (Submodule.subset_span (by simp))
theorem B_grade : B ∈ V := candidate_grade (Submodule.subset_span (by simp))
theorem C_grade : C4 ∈ V := candidate_grade (Submodule.subset_span (by simp))

include hInv hRel in
theorem word_zero (hC : f C4 = 0) (r : Fin 5) (i j k l : Fin 4) :
    f (word r (E i) (E j) (E k) (E l)) = 0 := by
  have hi := tensor_invariant f hInv
  have hs := tensor_symmetric f
  have hA : f A = 0 := (value_congr f hRel A_grade C_grade A_eq_C4).trans hC
  have hB : f B = 0 := by
    have he := value_congr f hRel B_grade (V.smul_mem (-1/2 : ℂ) C_grade)
      (show ScalarQuarticContractions.q B = ScalarQuarticContractions.q ((-1/2 : ℂ) • C4) by
        rw [map_smul]; exact B_eq_C4)
    rw [map_smul,hC,smul_zero] at he
    exact he
  have ha : (∑ a : Fin 4, ∑ b : Fin 4,
      LorentzRankFour.eta a*LorentzRankFour.eta b*LorentzRankFour.component (tensor f 2) a b a b) = 0 := by
    simpa only [A_word,map_sum,map_smul,smul_eq_mul,LorentzRankFour.component,tensor_apply,
      LorentzRankFour.eta,eta] using hA
  have hb : (∑ a : Fin 4, ∑ b : Fin 4,
      LorentzRankFour.eta a*LorentzRankFour.eta b*LorentzRankFour.component (tensor f 3) a b a b) = 0 := by
    simpa only [B_word,map_sum,map_smul,smul_eq_mul,LorentzRankFour.component,tensor_apply,
      LorentzRankFour.eta,eta] using hB
  have hc : (∑ a : Fin 4, ∑ b : Fin 4,
      LorentzRankFour.eta a*LorentzRankFour.eta b*LorentzRankFour.component (tensor f 4) a a b b) = 0 := by
    simpa only [C_word,map_sum,map_smul,smul_eq_mul,LorentzRankFour.component,tensor_apply,
      LorentzRankFour.eta,eta] using hC
  fin_cases r
  · exact LorentzRankFour.zero_of_trace_and_symmetric (tensor f 0) (hi 0) (hs 0)
      (extra_sym_zero f) (trace_zero f hRel 0) i j k l
  · exact LorentzRankFour.zero_of_trace_and_symmetric (tensor f 1) (hi 1) (hs 1)
      (extra_sym_one f) (trace_zero f hRel 1) i j k l
  · exact LorentzRankFour.zero_of_trace_and_cross (tensor f 2) (hi 2) (hs 2)
      (trace_zero f hRel 2) ha i j k l
  · exact LorentzRankFour.zero_of_trace_and_cross (tensor f 3) (hi 3) (hs 3)
      (trace_zero f hRel 3) hb i j k l
  · exact LorentzRankFour.zero_of_double_trace_and_symmetric (tensor f 4) (hi 4) (hs 4)
      (extra_sym_four f) hc i j k l

include hInv hRel in
theorem whole_grade_zero (hC : f C4 = 0) (p : V) : f p.val = 0 := by
  have hp : p.val ∈ ScalarQuarticFourSource.wordSpan := by
    rw [← ScalarQuarticFourSource.grade_eq_span]
    exact p.property
  refine Submodule.span_induction (p := fun p _ => f p = 0) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨r,i,j,k,l,rfl⟩
    exact word_zero f hInv hRel hC r i j k l
  · exact f.map_zero
  · intro p q _ _ hp hq
    rw [map_add,hp,hq,add_zero]
  · intro c p _ hp
    rw [map_smul,hp,smul_zero]

def generator : V := ⟨C4,C_grade⟩
def evaluate : selected.Coefficient →ₗ[ℂ] ℂ where
  toFun F := F.val generator
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem selected_zero (F : selected.Coefficient) (hF : evaluate F = 0) : F = 0 := by
  obtain ⟨f,hf⟩ := F.val.toLinearMap.exists_extend
  have he (p : OffShell) (hp : p ∈ V) : f p = F.val ⟨p,hp⟩ :=
    LinearMap.congr_fun hf ⟨p,hp⟩
  have hi : ∀ g p, p ∈ V → f (offAction g p) = f p := by
    intro g p hp
    rw [he p hp,he (offAction g p) (stable g hp)]
    exact F.val.isIntertwining _ _ g ⟨p,hp⟩
  have hr : ∀ p, p ∈ P.relations → p ∈ V → f p = 0 := by
    intro p hp hV
    rw [he p hV]
    exact F.property hp
  have hc : f C4 = 0 := (he C4 C_grade).trans hF
  apply Subtype.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  change F.val p = 0
  rw [← he p.val p.property]
  exact whole_grade_zero f hi hr hc p

theorem evaluate_injective : Function.Injective evaluate := by
  intro F G h
  apply sub_eq_zero.mp
  apply selected_zero
  change evaluate (F-G) = 0
  rw [map_sub,h,sub_self]

end
end Physics.ScalarQuarticFourUpper
