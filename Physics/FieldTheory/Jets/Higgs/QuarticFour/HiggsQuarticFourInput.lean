import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput
import Physics.FieldTheory.Jets.LorentzRankFour.Core.Invariant

/-! Actual whole-grade input and invariant contractions for the free H4D4 sector. -/
namespace Physics.HiggsQuarticFourInput
set_option autoImplicit false
noncomputable section
open Math MvPolynomial DerivativeLiteratureHiggs
abbrev P := HiggsStandardInput.input 0 0
abbrev V := ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 4 4

theorem stable : ∀ g, V ≤ V.comap (P.action g) := by
  intro g p hp
  exact JetFunctor.polynomialMap_homogeneous _
    (JetDirections.combined_order HiggsStandardInput.fields HiggsStandardInput.directions g) hp

def selected := P.select V stable

theorem h_grade (c : Bool) (a : Fin 2) :
    h c a ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 1 0 := by
  change (X ((c,a),0) : A).IsWeightedHomogeneous ScalarJetAlgebra.weight (1,0)
  simpa [ScalarJetAlgebra.weight,ScalarJetAlgebra.order] using
    isWeightedHomogeneous_X ℂ ScalarJetAlgebra.weight ((c,a),(0 : Fin 4 →₀ ℕ))

theorem first_grade (c : Bool) (i : Fin 4) (a : Fin 2) :
    first c i a ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 1 1 :=
  ScalarJetAlgebra.totalDerivative_mem i (h_grade c a)

theorem m_grade (i j : Fin 4) :
    m i j ∈ ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 2 :=
  Submodule.sum_mem _ (fun a _ => (first_grade true i a).mul (first_grade false j a))

theorem q1_grade : q1 ∈ V :=
  Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ =>
    Submodule.smul_mem _ _ ((m_grade i j).mul (m_grade j i))))
theorem q2_grade : q2 ∈ V :=
  Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ =>
    Submodule.smul_mem _ _ ((m_grade i j).mul (m_grade i j))))
theorem q3_grade : q3 ∈ V := by
  have hh : (∑ i : Fin 4, metric i • m i i) ∈
      ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 2 :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (m_grade i i))
  simpa [q3,pow_two,V,ScalarJetAlgebra.grade] using hh.mul hh

def representatives : Fin 3 → V := ![⟨q1,q1_grade⟩,⟨q2,q2_grade⟩,⟨q3,q3_grade⟩]

theorem first_X (c : Bool) (i : Fin 4) (a : Fin 2) :
    first c i a = X ((c,a),Finsupp.single i 1) := by
  simp [first,h,ScalarJetAlgebra.totalDerivative_X,ScalarJetAlgebra.shift]

theorem m_canonical (i j : Fin 4) :
    m i j = PairedJetContractions.canonical (ι := Fin 2)
      (Finsupp.single j 1) (Finsupp.single i 1) := by
  rw [PairedJetContractions.canonical_formula]
  simp only [m,first_X]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

theorem internal_m (g : StandardSMGaugeTensor.GaugeGroup) (i j : Fin 4) :
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g (m i j) = m i j := by
  rw [m_canonical]
  exact PairedJetContractions.canonical_invariant _ _ _ _

theorem internal_q1 (g : StandardSMGaugeTensor.GaugeGroup) :
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g q1 = q1 := by
  simp only [q1,map_sum,map_smul,map_mul,internal_m]
theorem internal_q2 (g : StandardSMGaugeTensor.GaugeGroup) :
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g q2 = q2 := by
  simp only [q2,map_sum,map_smul,map_mul,internal_m]
theorem internal_q3 (g : StandardSMGaugeTensor.GaugeGroup) :
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g q3 = q3 := by
  simp only [q3,map_pow,map_sum,map_smul,internal_m]

def directionCoefficient (g : LorentzDirections.Group) (i k : Fin 4) : ℂ :=
  (LorentzDirections.direction g (Finsupp.single i 1)) k

theorem contracted_coefficients (g : LorentzDirections.Group) (k l : Fin 4) :
    (∑ i : Fin 4, metric i*directionCoefficient g i k*directionCoefficient g i l) =
      LorentzRankFour.metric k l := by
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M k l)
    (LorentzRankFour.matrix_column g⁻¹)
  fin_cases k <;> fin_cases l
  all_goals simp [directionCoefficient,LorentzDirections.direction_single,
    LorentzRankFour.matrix,LorentzRankFour.J,LorentzRankFour.eta,LorentzRankFour.metric,
    metric,Matrix.mul_apply,Matrix.transpose_apply,LinearMap.toMatrix'_apply,
    Fin.sum_univ_succ] at he ⊢
  all_goals linear_combination he

def dot (x y : Fin 4 → A) : A := ∑ i : Fin 4, metric i • (x i*y i)

theorem dot_covariant (g : LorentzDirections.Group) (x y : Fin 4 → A) :
    dot (fun i => ∑ k : Fin 4, directionCoefficient g i k • x k)
      (fun i => ∑ k : Fin 4, directionCoefficient g i k • y k) = dot x y := by
  calc
    _ = ∑ k : Fin 4, ∑ l : Fin 4,
        (∑ i : Fin 4, metric i*directionCoefficient g i k*directionCoefficient g i l) •
          (x k*y l) := by
      conv_rhs => rw [Finset.sum_comm]
      simp only [dot,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
        Finset.smul_sum,Finset.sum_smul,smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    _ = dot x y := by
      simp only [contracted_coefficients]
      simp [LorentzRankFour.metric,dot,metric,Fin.sum_univ_succ]
      abel

theorem pair_dot (p q : A) : pair p q = dot (fun i => D i p) (fun i => D i q) := by
  simp [pair,dot,metric,Fin.sum_univ_succ]
  abel

theorem lorentz_pair (g : LorentzDirections.Group) (p q : A) :
    HiggsLagrangianInput.transport g (pair p q) =
      pair (HiggsLagrangianInput.transport g p) (HiggsLagrangianInput.transport g q) := by
  rw [pair_dot,pair_dot]
  change HiggsLagrangianInput.transport g (∑ i : Fin 4, metric i • (D i p*D i q)) = _
  simp only [map_sum,map_smul,map_mul,HiggsLagrangianInput.covariance]
  exact dot_covariant g _ _

theorem q1_pairs : q1 = ∑ a : Fin 2, ∑ b : Fin 2,
    pair (h true a) (h false b)*pair (h true b) (h false a) := by
  norm_num [q1,m,first,pair,metric,Fin.sum_univ_succ]
  ring
theorem q2_pairs : q2 = ∑ a : Fin 2, ∑ b : Fin 2,
    pair (h true a) (h true b)*pair (h false a) (h false b) := by
  norm_num [q2,m,first,pair,metric,Fin.sum_univ_succ]
  ring
theorem q3_pairs : q3 = (∑ a : Fin 2, pair (h true a) (h false a))^2 := by
  norm_num [q3,m,first,pair,metric,Fin.sum_univ_succ]
  ring

theorem lorentz_q1 (g : LorentzDirections.Group) :
    HiggsLagrangianInput.transport g q1 = q1 := by
  rw [q1_pairs]
  simp only [map_sum,map_mul,lorentz_pair,HiggsLagrangianInput.field_invariant]
theorem lorentz_q2 (g : LorentzDirections.Group) :
    HiggsLagrangianInput.transport g q2 = q2 := by
  rw [q2_pairs]
  simp only [map_sum,map_mul,lorentz_pair,HiggsLagrangianInput.field_invariant]
theorem lorentz_q3 (g : LorentzDirections.Group) :
    HiggsLagrangianInput.transport g q3 = q3 := by
  rw [q3_pairs]
  simp only [map_sum,map_pow,lorentz_pair,HiggsLagrangianInput.field_invariant]

theorem invariant_q1 (g : HiggsStandardInput.Group) : HiggsStandardInput.transport g q1 = q1 := by
  rw [HiggsStandardInput.factorize,lorentz_q1,internal_q1]
theorem invariant_q2 (g : HiggsStandardInput.Group) : HiggsStandardInput.transport g q2 = q2 := by
  rw [HiggsStandardInput.factorize,lorentz_q2,internal_q2]
theorem invariant_q3 (g : HiggsStandardInput.Group) : HiggsStandardInput.transport g q3 = q3 := by
  rw [HiggsStandardInput.factorize,lorentz_q3,internal_q3]

def evaluate : selected.Coefficient →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun F i := F.val (representatives i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Physics.HiggsQuarticFourInput
