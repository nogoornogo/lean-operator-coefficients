import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourWaves

/-! Three complete-relation separators on the actual Higgs source.
They certify quotient independence; individual waves are not invariant coefficients. -/
namespace Physics.HiggsQuarticFourSeparation
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs HiggsQuarticFourInput
open FourWavePolarization

def slot (j : Label) : Fin 4 := if j.1 then ![2,3] j.2 else ![0,1] j.2
def amplitudes (j : Label) : Fin 4 → ℂ := Pi.single (slot j) 1
def momenta (r : Fin 3) : Fin 4 → Fin 4 → ℂ := ![
  ![![1,0,0,1],![1,0,0,-1],![-1,-1,0,0],![-1,1,0,0]],
  ![![1,0,0,1],![1,0,0,-1],![-1,0,0,-1],![-1,0,0,1]],
  ![![1,0,0,1],![1,0,0,-1],![-1,0,0,1],![-1,0,0,-1]]] r

theorem conservation (r : Fin 3) (i : Fin 4) : ∑ s : Fin 4, momenta r s i = 0 := by
  fin_cases r <;> fin_cases i <;> norm_num [momenta,Fin.sum_univ_succ]
theorem null (r : Fin 3) (s : Fin 4) :
    (momenta r s 0)^2-(momenta r s 1)^2-(momenta r s 2)^2-(momenta r s 3)^2 = 0 := by
  fin_cases r <;> fin_cases s <;> norm_num [momenta]

def separator (r : Fin 3) : A →ₗ[ℂ] ℂ :=
  ColoredFourWaveEvaluation.onJets (momenta r) amplitudes
theorem annihilates (r : Fin 3) : P.relations ≤ (separator r).ker :=
  HiggsQuarticFourWaves.annihilates _ _ (conservation r) (null r)
def quotient (r : Fin 3) : P.Source →ₗ[ℂ] ℂ := P.relations.liftQ (separator r) (annihilates r)
@[simp] theorem quotient_projection (r : Fin 3) (p : A) :
    quotient r (P.projection p) = separator r p := rfl

theorem evaluation_first (r : Fin 3) (c : Bool) (i : Fin 4) (a : Fin 2) :
    ColoredFourWaveEvaluation.evaluation (momenta r) amplitudes (first c i a) =
      momenta r (slot (c,a)) i • (X (slot (c,a)) : FourWaveEvaluation.P) := by
  rw [first,h,ColoredFourWaveEvaluation.first_value]
  simp [linear,amplitudes,Pi.single_apply]

def values : Fin 3 → Fin 3 → ℂ := ![![2,8,2],![8,8,0],![0,8,8]]

theorem q1_value (r : Fin 3) : separator r q1 = values r 0 := by
  change FourWaveEvaluation.coefficient
    (ColoredFourWaveEvaluation.evaluation (momenta r) amplitudes q1) = _
  simp only [q1,m,map_sum,map_smul,map_mul,evaluation_first]
  fin_cases r
  all_goals norm_num [metric,momenta,slot,Fin.sum_univ_succ,values,
    FourWaveEvaluation.coefficient,MvPolynomial.lcoeff_apply,
    MvPolynomial.smul_eq_C_mul,X_pow_eq_monomial,X,
    C_mul_monomial,monomial_mul_monomial,coeff_monomial,
    mul_add,add_mul,neg_mul,mul_neg,neg_neg,map_add,coeff_neg,
    FourWaveEvaluation.squareFree,Finsupp.ext_iff,Fin.forall_fin_succ]

theorem q2_value (r : Fin 3) : separator r q2 = values r 1 := by
  change FourWaveEvaluation.coefficient
    (ColoredFourWaveEvaluation.evaluation (momenta r) amplitudes q2) = _
  simp only [q2,m,map_sum,map_smul,map_mul,evaluation_first]
  fin_cases r
  all_goals norm_num [metric,momenta,slot,Fin.sum_univ_succ,values,
    FourWaveEvaluation.coefficient,MvPolynomial.lcoeff_apply,
    MvPolynomial.smul_eq_C_mul,X_pow_eq_monomial,X,
    C_mul_monomial,monomial_mul_monomial,coeff_monomial,
    mul_add,add_mul,neg_mul,mul_neg,neg_neg,map_add,coeff_neg,
    FourWaveEvaluation.squareFree,Finsupp.ext_iff,Fin.forall_fin_succ]

theorem q3_value (r : Fin 3) : separator r q3 = values r 2 := by
  change FourWaveEvaluation.coefficient
    (ColoredFourWaveEvaluation.evaluation (momenta r) amplitudes q3) = _
  simp only [q3,m,map_sum,map_smul,map_mul,evaluation_first,pow_two]
  fin_cases r
  all_goals norm_num [metric,momenta,slot,Fin.sum_univ_succ,values,
    FourWaveEvaluation.coefficient,MvPolynomial.lcoeff_apply,
    MvPolynomial.smul_eq_C_mul,X_pow_eq_monomial,X,
    C_mul_monomial,monomial_mul_monomial,coeff_monomial,
    mul_add,add_mul,neg_mul,mul_neg,neg_neg,map_add,coeff_neg,
    FourWaveEvaluation.squareFree,Finsupp.ext_iff,Fin.forall_fin_succ]

theorem representative_value (r i : Fin 3) :
    separator r (representatives i).val = values r i := by
  fin_cases i
  · exact q1_value r
  · exact q2_value r
  · exact q3_value r

def inverseMatrix : Fin 3 → Fin 3 → ℂ := ![
  ![-1/4,3/16,1/16],![1/4,-1/16,-1/16],![-1/4,1/16,3/16]]
def decoder (i : Fin 3) : P.Source →ₗ[ℂ] ℂ :=
  ∑ r : Fin 3, inverseMatrix i r • quotient r

theorem decoder_value (i j : Fin 3) :
    decoder i (P.projection (representatives j).val) = if i = j then 1 else 0 := by
  change (∑ r : Fin 3, inverseMatrix i r • quotient r)
    (P.projection (representatives j).val) = _
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply,quotient_projection,representative_value,smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [inverseMatrix,values,Fin.sum_univ_succ]

def coordinates : P.Source →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi decoder
def combination : (Fin 3 → ℂ) →ₗ[ℂ] P.Source where
  toFun c := ∑ i : Fin 3, c i • P.projection (representatives i).val
  map_add' c d := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' z c := by simp [Finset.smul_sum,smul_smul]

theorem coordinates_combination (c : Fin 3 → ℂ) : coordinates (combination c) = c := by
  funext i
  change decoder i (∑ j : Fin 3, c j • P.projection (representatives j).val) = c i
  simp only [map_sum,map_smul,decoder_value]
  simp

theorem combination_injective : Function.Injective combination :=
  Function.LeftInverse.injective coordinates_combination

abbrev CandidateImage := LinearMap.range combination
def candidateEquivalence : CandidateImage ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toLinearMap := coordinates.comp (LinearMap.range combination).subtype
  invFun c := ⟨combination c,⟨c,rfl⟩⟩
  left_inv x := by
    obtain ⟨c,hc⟩ := x.property
    apply Subtype.ext
    change combination (coordinates x.val) = x.val
    rw [← hc,coordinates_combination]
  right_inv c := coordinates_combination c

theorem candidate_dimension : Module.finrank ℂ CandidateImage = 3 := by
  rw [candidateEquivalence.finrank_eq]
  simp

/-- The entire relation module cannot produce a dependence of these candidates. -/
theorem independent_mod_relations (a b c : ℂ)
    (hz : a • q1+b • q2+c • q3 ∈ P.relations) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := annihilates 0 hz
  have h1 := annihilates 1 hz
  have h2 := annihilates 2 hz
  change separator 0 (a • q1+b • q2+c • q3) = 0 at h0
  change separator 1 (a • q1+b • q2+c • q3) = 0 at h1
  change separator 2 (a • q1+b • q2+c • q3) = 0 at h2
  simp only [map_add,map_smul,q1_value,q2_value,q3_value,smul_eq_mul] at h0 h1 h2
  norm_num [values] at h0 h1 h2
  refine ⟨?_,?_,?_⟩
  · linear_combination (-1/4:ℂ)*h0+(3/16:ℂ)*h1+(1/16:ℂ)*h2
  · linear_combination (1/4:ℂ)*h0-(1/16:ℂ)*h1-(1/16:ℂ)*h2
  · linear_combination (-1/4:ℂ)*h0+(1/16:ℂ)*h1+(3/16:ℂ)*h2

end
end Physics.HiggsQuarticFourSeparation
