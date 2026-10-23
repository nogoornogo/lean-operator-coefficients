import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWitness
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticTwoCompleteness

/-! Exact free EOM/IBP reduction of three specified quartic metric contractions.
Coverage of all invariant coefficients at derivative order four is not assumed. -/
namespace Physics.ScalarQuarticContractions
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM
abbrev q := (ScalarDerivativeInterface.scalar 0).projection
abbrev eta : Fin 4 → ℂ := ![1,-1,-1,-1]
abbrev K := LorentzJetIBP.kinetic
abbrev W := LorentzJetIBP.waveField

def A : OffShell := field^2 * ∑ i : Fin 4, ∑ j : Fin 4,
  (eta i*eta j) • (D i (D j field))^2
def B : OffShell := field * ∑ i : Fin 4, ∑ j : Fin 4,
  (eta i*eta j) • (D i (D j field)*D i field*D j field)
abbrev C4 := DerivativeLiteratureScalar.fourDerivative

theorem kinetic_sum : K = ∑ i : Fin 4, eta i • (D i field)^2 := by
  unfold K
  rw [DerivativeLiteratureScalar.kinetic_as_derivatives]
  simp [eta,Fin.sum_univ_succ]
  ring
theorem wave_sum : W = ∑ i : Fin 4, eta i • D i (D i field) := by
  unfold W
  rw [MasslessScalarEOM.waveField_formula]
  simp [eta,Fin.sum_univ_succ,field,MasslessScalarEOM.field,D,ScalarJetAlgebra.shift,
    ← Finsupp.single_add]
  ring

theorem wave_mem : W ∈ ideal 0 := by
  have h := DifferentialEquation.seed_mem D (equations 0) (Set.mem_singleton (seed 0))
  simpa [seed] using h

theorem divergence_zero (i : Fin 4) (p : OffShell) : q (D i p) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right
    (DifferentialEquation.derivative_mem_ibp D i p))
theorem ideal_zero {p : OffShell} (hp : p ∈ ideal 0) : q p = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_left hp)

theorem C4_relation : q C4 = (-2 : ℂ) • q B := by
  have he : (∑ i : Fin 4, D i (eta i • (field*D i field*K))) =
      C4+field*K*W+(2:ℂ) • B := by
    dsimp only [C4,DerivativeLiteratureScalar.fourDerivative]
    simp only [wave_sum,kinetic_sum]
    simp [B,eta,Fin.sum_univ_succ,MvPolynomial.smul_eq_C_mul]
    norm_num only [map_ofNat]
    ring
  have hd : q (∑ i : Fin 4, D i (eta i • (field*D i field*K))) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => divergence_zero i _)
  have hw : q (field*K*W) = 0 := ideal_zero ((ideal 0).mul_mem_left _ wave_mem)
  rw [he,map_add,map_add,hw,add_zero,map_smul] at hd
  exact (eq_neg_of_add_eq_zero_left hd).trans (by simp)

theorem third_commute (i j : Fin 4) : D i (D i (D j field)) = D j (D i (D i field)) := by
  rw [ScalarJetAlgebra.totalDerivative_commute i j field,
    ScalarJetAlgebra.totalDerivative_commute i j (D i field)]

theorem differentiated_inner (i j : Fin 4) :
    D i (field^2*(D j field*D i (D j field))) =
      2*field*D i field*D j field*D i (D j field)+field^2*(D i (D j field))^2+
      field^2*D j field*D j (D i (D i field)) := by
  simp only [pow_two,ScalarJetAlgebra.totalDerivative_mul]
  rw [third_commute]
  ring

theorem A_relation : q A = (-2 : ℂ) • q B := by
  let remainder : OffShell := field^2 * ∑ j : Fin 4, eta j • (D j field*D j W)
  have hr : remainder ∈ ideal 0 := by
    apply (ideal 0).mul_mem_left
    apply Submodule.sum_mem
    intro j _
    exact (DifferentialEquation.relations D (equations 0)).smul_mem _
      ((ideal 0).mul_mem_left _ (DifferentialEquation.stable D (equations 0) j wave_mem))
  have he : (∑ i : Fin 4, D i (eta i • (field^2 *
      ∑ j : Fin 4, eta j • (D j field*D i (D j field))))) =
      A+(2:ℂ) • B+remainder := by
    dsimp only [remainder]
    rw [wave_sum]
    simp only [A,B,Derivation.map_smul,map_sum,Finset.mul_sum,mul_smul_comm,differentiated_inner]
    simp only [eta,Fin.sum_univ_succ]
    simp [MvPolynomial.smul_eq_C_mul]
    norm_num only [map_ofNat]
    ring
  have hd : q (∑ i : Fin 4, D i (eta i • (field^2 *
      ∑ j : Fin 4, eta j • (D j field*D i (D j field))))) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => divergence_zero i _)
  rw [he,map_add,map_add,ideal_zero hr,add_zero,map_smul] at hd
  exact (eq_neg_of_add_eq_zero_left hd).trans (by simp)

theorem A_eq_C4 : q A = q C4 := (A_relation).trans C4_relation.symm
theorem A_nonzero : q A ≠ 0 := by
  rw [A_eq_C4]
  exact ScalarQuarticFourWitness.quotient_nonzero
theorem B_nonzero : q B ≠ 0 := by
  intro h
  have he := C4_relation
  rw [h,smul_zero] at he
  exact ScalarQuarticFourWitness.quotient_nonzero he

theorem B_eq_C4 : q B = (-1/2 : ℂ) • q C4 := by
  have h := congrArg (fun p => (-1/2 : ℂ) • p) C4_relation
  norm_num only [smul_smul] at h
  simpa only [one_smul,neg_div] using h.symm

def candidateSource : Submodule ℂ OffShell := Submodule.span ℂ {A,B,C4}
def candidateImage := candidateSource.map q

theorem candidate_image_eq : candidateImage = Submodule.span ℂ {q C4} := by
  apply le_antisymm
  · rw [candidateImage,candidateSource,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    rcases hp with rfl | rfl | rfl
    · rw [A_eq_C4]
      exact Submodule.subset_span (Set.mem_singleton _)
    · rw [B_eq_C4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.subset_span (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact Submodule.mem_map.mpr ⟨C4,Submodule.subset_span (by simp),rfl⟩

theorem candidate_image_dimension : Module.finrank ℂ candidateImage = 1 := by
  rw [candidate_image_eq]
  exact finrank_span_singleton ScalarQuarticFourWitness.quotient_nonzero

theorem candidate_grade : candidateSource ≤ ScalarJetAlgebra.grade 4 4 := by
  open ScalarQuarticTwoCompleteness in
  have hA : A ∈ ScalarJetAlgebra.grade 4 4 := by
    have hs : (∑ i : Fin 4, ∑ j : Fin 4, (eta i*eta j) • (D i (D j field))^2) ∈
        ScalarJetAlgebra.grade 2 4 :=
      Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ =>
        Submodule.smul_mem _ _ ((ScalarJetAlgebra.totalDerivative_mem i (first_grade j)).pow 2)))
    exact (field_power_grade 2).mul hs
  open ScalarQuarticTwoCompleteness in
  have hB : B ∈ ScalarJetAlgebra.grade 4 4 := by
    have hs : (∑ i : Fin 4, ∑ j : Fin 4, (eta i*eta j) •
        (D i (D j field)*D i field*D j field)) ∈ ScalarJetAlgebra.grade 3 4 :=
      Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ =>
        Submodule.smul_mem _ _ (((ScalarJetAlgebra.totalDerivative_mem i (first_grade j)).mul
          (first_grade i)).mul (first_grade j))))
    exact field_grade.mul hs
  open ScalarQuarticTwoCompleteness in
  have hK : K ∈ ScalarJetAlgebra.grade 2 2 := by
    rw [kinetic_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ((first_grade i).pow 2))
  have hC : C4 ∈ ScalarJetAlgebra.grade 4 4 := hK.pow 2
  apply Submodule.span_le.mpr
  rintro p (rfl | rfl | rfl)
  · exact hA
  · exact hB
  · exact hC

theorem C4_fixed (g : LorentzDirections.Group) :
    (ScalarDerivativeInterface.scalar 0).residual g (q C4) = q C4 := by
  change q (offAction g C4) = q C4
  rw [DerivativeLiteratureScalar.four_invariant]

theorem candidate_image_fixed (g : LorentzDirections.Group) (x : candidateImage) :
    (ScalarDerivativeInterface.scalar 0).residual g x.val = x.val := by
  have hx : x.val ∈ Submodule.span ℂ {q C4} := by
    rw [← candidate_image_eq]
    exact x.property
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [← hc,map_smul,C4_fixed]

end
end Physics.ScalarQuarticContractions
