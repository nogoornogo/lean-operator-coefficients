import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalControls
import Math.LinearAlgebra.Constructions.SevenScalarConstraints

/-! Internal constraints on all first-derivative scalar contractions. -/
-- Check finite certificates sequentially to avoid blocked elaboration worker stacks.
set_option Elab.async false

namespace Physics.HiggsQuarticFourInternalUpper
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls

theorem pair_comm (p q : A) : pair p q = pair q p := by
  unfold pair
  ring
theorem pair_add_left (p q r : A) : pair (p+q) r = pair p r+pair q r := by
  simp only [pair,map_add]
  ring
theorem pair_add_right (p q r : A) : pair p (q+r) = pair p q+pair p r := by
  simp only [pair,map_add]
  ring
theorem pair_sub_left (p q r : A) : pair (p-q) r = pair p r-pair q r := by
  simp only [pair,map_sub]
  ring
theorem pair_sub_right (p q r : A) : pair p (q-r) = pair p q-pair p r := by
  simp only [pair,map_sub]
  ring
theorem pair_smul_left (c : ℂ) (p q : A) : pair (c • p) q = c • pair p q := by
  simp only [pair,Derivation.map_smul,smul_mul_assoc,smul_sub]
theorem pair_smul_right (c : ℂ) (p q : A) : pair p (c • q) = c • pair p q := by
  simp only [pair,Derivation.map_smul,mul_smul_comm,smul_sub]
theorem pair_transport (g : StandardSMGaugeTensor.GaugeGroup) (p q : A) :
    T g (pair p q) = pair (T g p) (T g q) := by
  simp only [pair,map_sub,map_mul,HiggsInternalSymmetry.derivative_commute]

def K (i j k l : Fin 4) : A := pair (field i) (field j)*pair (field k) (field l)
theorem field_pairs (i j k l : Fin 4) :
    pair (field i) (field j)*pair (field k) (field l) = K i j k l := rfl
theorem K_left (i j k l : Fin 4) : K i j k l = K j i k l :=
  congrArg (fun p : A => p*pair (field k) (field l)) (pair_comm (field i) (field j))
theorem K_right (i j k l : Fin 4) : K i j k l = K i j l k :=
  congrArg (fun p : A => pair (field i) (field j)*p) (pair_comm (field k) (field l))
theorem K_swap (i j k l : Fin 4) : K i j k l = K k l i j := mul_comm _ _

theorem K_grade (i j k l : Fin 4) : K i j k l ∈ HiggsQuarticFourInput.V := by
  have hp (i j : Fin 4) : pair (field i) (field j) ∈
      ScalarJetAlgebra.grade (S := Label) (I := Fin 4) 2 2 := by
    rw [HiggsQuarticFourInput.pair_dot]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.smul_mem
    exact (ScalarJetAlgebra.totalDerivative_mem a (HiggsQuarticFourInput.h_grade _ _)).mul
      (ScalarJetAlgebra.totalDerivative_mem a (HiggsQuarticFourInput.h_grade _ _))
  exact (hp i j).mul (hp k l)

theorem numerator_nontrivial : ∀ i j k l : Fin 4,
    weight i+weight j+weight k+weight l ≠ 0 →
      numerator i*numerator j*numerator k*numerator l ≠ (625 : GaussianInt)^4 := by
  decide +kernel

theorem eigen_nontrivial (i j k l : Fin 4) (hw : weight i+weight j+weight k+weight l ≠ 0) :
    eigen i*eigen j*eigen k*eigen l-1 ≠ 0 := by
  intro hz
  have hc : GaussianInt.toComplex (numerator i*numerator j*numerator k*numerator l) =
      GaussianInt.toComplex ((625 : GaussianInt)^4) := by
    simp only [map_mul,map_pow,map_ofNat]
    dsimp only [eigen] at hz
    linear_combination (625 : ℂ)^4 * hz
  exact numerator_nontrivial i j k l hw (GaussianInt.toComplex_injective hc)

def rotateField : Fin 4 → A := ![
  (3/5 : ℂ) • field 0-(4/5 : ℂ) • field 1,
  (4/5 : ℂ) • field 0+(3/5 : ℂ) • field 1,
  (3/5 : ℂ) • field 2-(4/5 : ℂ) • field 3,
  (4/5 : ℂ) • field 2+(3/5 : ℂ) • field 3]
theorem rotation_field4 (i : Fin 4) : T rotationGroup (field i) = rotateField i := by
  fin_cases i
  · simpa [field,label,rotateField] using rotation_field false 0
  · simpa [field,label,rotateField] using rotation_field false 1
  · simpa [field,label,rotateField] using rotation_field true 0
  · simpa [field,label,rotateField] using rotation_field true 1

theorem q1_K : q1 = K 0 2 0 2+K 1 3 1 3+(2 : ℂ) • K 0 3 1 2 := by
  rw [HiggsQuarticFourInput.q1_pairs]
  simp [Fin.sum_univ_two,K,field,label,pair_comm,two_smul]
  ring
theorem q2_K : q2 = K 0 0 2 2+K 1 1 3 3+(2 : ℂ) • K 0 1 2 3 := by
  rw [HiggsQuarticFourInput.q2_pairs]
  simp [Fin.sum_univ_two,K,field,label,pair_comm,two_smul]
  ring
theorem q3_K : q3 = K 0 2 0 2+K 1 3 1 3+(2 : ℂ) • K 0 2 1 3 := by
  rw [HiggsQuarticFourInput.q3_pairs]
  simp [Fin.sum_univ_two,K,field,label,pair_comm,two_smul]
  ring

variable (f : A →ₗ[ℂ] ℂ)
  (hInternal : ∀ g p, p ∈ HiggsQuarticFourInput.V → f (T g p) = f p)

include hInternal in
theorem vanish (i j k l : Fin 4) (hw : weight i+weight j+weight k+weight l ≠ 0) :
    f (K i j k l) = 0 := by
  have he := hInternal phaseGroup (K i j k l) (K_grade i j k l)
  change f (T phaseGroup (pair (field i) (field j)*pair (field k) (field l))) = f (K i j k l) at he
  simp only [map_mul,pair_transport,phase_field,pair_smul_left,pair_smul_right,
    smul_mul_assoc,mul_smul_comm,smul_smul,map_smul,smul_eq_mul] at he
  simp only [field_pairs] at he
  have hz : (eigen i*eigen j*eigen k*eigen l-1)*f (K i j k l) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (eigen_nontrivial i j k l hw)

include hInternal in
theorem rotation_row0 : 108*f (K 0 0 2 2)+168*f (K 0 1 2 3)-192*f (K 1 1 3 3) = 0 := by
  have he := hInternal rotationGroup (K 0 0 2 3) (K_grade 0 0 2 3)
  change f (T rotationGroup (pair (field 0) (field 0)*pair (field 2) (field 3))) = f (K 0 0 2 3) at he
  simp only [map_mul,pair_transport,rotation_field4] at he
  norm_num [rotateField] at he
  simp only [pair_add_right,pair_sub_left,pair_sub_right,pair_smul_left,pair_smul_right,
    smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub,mul_add,map_add,map_sub,map_smul,
    smul_eq_mul] at he
  simp only [field_pairs] at he
  simp (disch := decide +kernel) only [vanish f hInternal] at he
  simp only [K_left,K_right] at he ⊢
  linear_combination (625 : ℂ)*he

include hInternal in
theorem rotation_row1 : 144*f (K 0 0 2 2)-576*f (K 0 1 2 3)+144*f (K 1 1 3 3) = 0 := by
  have he := hInternal rotationGroup (K 0 0 3 3) (K_grade 0 0 3 3)
  change f (T rotationGroup (pair (field 0) (field 0)*pair (field 3) (field 3))) = f (K 0 0 3 3) at he
  simp only [map_mul,pair_transport,rotation_field4] at he
  norm_num [rotateField] at he
  simp only [pair_add_left,pair_add_right,pair_sub_left,pair_sub_right,pair_smul_left,pair_smul_right,
    smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub,mul_add,map_add,map_sub,map_smul,
    smul_eq_mul] at he
  simp only [field_pairs] at he
  simp (disch := decide +kernel) only [vanish f hInternal] at he
  simp only [K_left,K_right] at he ⊢
  linear_combination (625 : ℂ)*he

include hInternal in
theorem rotation_row2 : 108*f (K 0 2 0 2)+84*f (K 0 2 1 3)-192*f (K 1 3 1 3)+84*f (K 0 3 1 2) = 0 := by
  have he := hInternal rotationGroup (K 0 2 0 3) (K_grade 0 2 0 3)
  change f (T rotationGroup (pair (field 0) (field 2)*pair (field 0) (field 3))) = f (K 0 2 0 3) at he
  simp only [map_mul,pair_transport,rotation_field4] at he
  norm_num [rotateField] at he
  simp only [pair_add_right,pair_sub_left,pair_sub_right,pair_smul_left,pair_smul_right,
    smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub,mul_add,map_add,map_sub,map_smul,
    smul_eq_mul] at he
  simp only [field_pairs] at he
  simp (disch := decide +kernel) only [vanish f hInternal] at he
  simp only [K_swap] at he ⊢
  linear_combination (625 : ℂ)*he

include hInternal in
theorem rotation_row3 : 144*f (K 0 2 0 2)-288*f (K 0 2 1 3)+144*f (K 1 3 1 3)-288*f (K 0 3 1 2) = 0 := by
  have he := hInternal rotationGroup (K 0 3 0 3) (K_grade 0 3 0 3)
  change f (T rotationGroup (pair (field 0) (field 3)*pair (field 0) (field 3))) = f (K 0 3 0 3) at he
  simp only [map_mul,pair_transport,rotation_field4] at he
  norm_num [rotateField] at he
  simp only [pair_add_right,pair_sub_left,pair_smul_left,pair_smul_right,
    smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub,mul_add,add_mul,map_add,map_sub,map_smul,
    smul_eq_mul] at he
  simp only [field_pairs] at he
  simp (disch := decide +kernel) only [vanish f hInternal] at he
  simp only [K_swap] at he ⊢
  linear_combination (625 : ℂ)*he

def seven : Fin 7 → A := ![K 0 0 2 2,K 0 1 2 3,K 1 1 3 3,
  K 0 2 0 2,K 0 2 1 3,K 1 3 1 3,K 0 3 1 2]

include hInternal in
theorem seven_zero (h1 : f q1 = 0) (h2 : f q2 = 0) (h3 : f q3 = 0) (i : Fin 7) :
    f (seven i) = 0 := by
  have r0 := rotation_row0 f hInternal
  have r1 := rotation_row1 f hInternal
  have r2 := rotation_row2 f hInternal
  have r3 := rotation_row3 f hInternal
  rw [q1_K,map_add,map_add,map_smul,smul_eq_mul] at h1
  rw [q2_K,map_add,map_add,map_smul,smul_eq_mul] at h2
  rw [q3_K,map_add,map_add,map_smul,smul_eq_mul] at h3
  have hz := SevenScalarConstraints.zero
    (f (K 0 0 2 2)) (f (K 0 1 2 3)) (f (K 1 1 3 3))
    (f (K 0 2 0 2)) (f (K 0 2 1 3)) (f (K 1 3 1 3)) (f (K 0 3 1 2))
    r0 r1 r2 r3 h1 h2 h3
  fin_cases i
  · exact hz.1
  · exact hz.2.1
  · exact hz.2.2.1
  · exact hz.2.2.2.1
  · exact hz.2.2.2.2.1
  · exact hz.2.2.2.2.2.1
  · exact hz.2.2.2.2.2.2


end
end Physics.HiggsQuarticFourInternalUpper
