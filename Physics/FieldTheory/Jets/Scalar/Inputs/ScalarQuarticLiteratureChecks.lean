import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourChecks
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate

/-! Native scalar coefficient comparisons with 1706.08520v1 (6.3),
2105.12742v3 (3.28)-(3.29), and 1510.00372v1 (2.8).
The paper densities are inputs to the entire selected Lorentz coefficient
space. No Euclidean, conformal-primary or amplitude equivalence is assumed. -/
namespace Physics.ScalarQuarticLiteratureChecks
set_option autoImplicit false
noncomputable section
open Math PolynomialScalarEOM ScalarQuarticFourTensors
open ScalarQuarticFourCompleteness ScalarQuarticContractions

/-- The zero-order entry is the actual image; positive entries are invariant duals. -/
theorem bounded_counts :
    Module.finrank ℂ (ScalarZeroDerivativeCertificate.Image 4) = 1 ∧
    Module.finrank ℂ ScalarQuarticTwoCompleteness.selected.Coefficient = 0 ∧
    Module.finrank ℂ selected.Coefficient = 1 :=
  ⟨ScalarZeroDerivativeCertificate.four_scalar_dimension,
    ScalarQuarticTwoCompleteness.coefficient_dimension,coefficient_dimension⟩

def first : V := ⟨ScalarCompletenessChecks.Cao.o1,
  V.smul_mem _ ScalarQuarticFourUpper.A_grade⟩
def second : V := ⟨ScalarCompletenessChecks.Cao.o2,
  V.smul_mem _ ScalarQuarticFourUpper.B_grade⟩
def third : V := ⟨ScalarCompletenessChecks.Cao.o3,
  V.smul_mem _ ScalarQuarticFourUpper.C_grade⟩
def chosen : V := first-(2:ℂ) • second+(6:ℂ) • third

theorem chosen_density : chosen.val = ScalarCompletenessChecks.Cao.combination := rfl

theorem normalized_first : normalized.val first = (1/4:ℂ) := by
  change functional ((1/4:ℂ) • A) = _
  rw [map_smul,ScalarQuarticFourChecks.A_value]
  norm_num

theorem normalized_second : normalized.val second = (-1/4:ℂ) := by
  change functional ((1/2:ℂ) • B) = _
  rw [map_smul,ScalarQuarticFourChecks.B_value]
  norm_num

theorem normalized_third : normalized.val third = (1/8:ℂ) := by
  change functional ((1/8:ℂ) • C4) = _
  rw [map_smul,normalization]
  norm_num

theorem value (F : selected.Coefficient) (p : V) :
    F.val p = equivalence F * normalized.val p := by
  have h := congrArg (fun G : selected.Coefficient => G.val p) (reconstruction F)
  exact h.symm

theorem first_value (F : selected.Coefficient) :
    F.val first = (1/4:ℂ)*equivalence F := by
  rw [value,normalized_first,mul_comm]

theorem second_value (F : selected.Coefficient) :
    F.val second = (-1/4:ℂ)*equivalence F := by
  rw [value,normalized_second,mul_comm]

theorem third_value (F : selected.Coefficient) :
    F.val third = (1/8:ℂ)*equivalence F := by
  rw [value,normalized_third,mul_comm]

theorem chosen_value (F : selected.Coefficient) :
    F.val chosen = (3/2:ℂ)*equivalence F := by
  simp only [chosen,map_add,map_sub,map_smul,smul_eq_mul,first_value,second_value,third_value]
  ring

/-- The paper's chosen density determines all admitted coefficients, not just candidates. -/
def chosenEquivalence : selected.Coefficient ≃ₗ[ℂ] ℂ where
  toLinearMap := {
    toFun F := F.val chosen
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  invFun c := ((2/3:ℂ)*c) • normalized
  left_inv F := by
    apply equivalence.injective
    change equivalence (((2/3:ℂ)*F.val chosen) • normalized) = equivalence F
    rw [map_smul,show equivalence normalized = 1 from normalized_value,chosen_value]
    simp only [smul_eq_mul]
    ring
  right_inv c := by
    change (((2/3:ℂ)*c) • normalized).val chosen = c
    rw [chosen_value,map_smul,show equivalence normalized = 1 from normalized_value]
    simp only [smul_eq_mul]
    ring

@[simp] theorem chosen_extraction (F : selected.Coefficient) :
    chosenEquivalence F = F.val chosen := rfl

@[simp] theorem chosen_inverse (c : ℂ) :
    chosenEquivalence.symm c = ((2/3:ℂ)*c) • normalized := rfl

theorem chosen_reconstruction (F : selected.Coefficient) :
    ((2/3:ℂ)*F.val chosen) • normalized = F :=
  chosenEquivalence.symm_apply_apply F

/-- Necessary and sufficient compatibility for the three paper-normalized values. -/
theorem admitted_triple (a b c : ℂ) :
    (∃! F : selected.Coefficient,
      F.val first = a ∧ F.val second = b ∧ F.val third = c) ↔
    b = -a ∧ a = 2*c := by
  constructor
  · rintro ⟨F,⟨ha,hb,hc⟩,_⟩
    rw [first_value] at ha
    rw [second_value] at hb
    rw [third_value] at hc
    constructor
    · linear_combination -hb-ha
    · linear_combination -ha+2*hc
  · rintro ⟨rfl,rfl⟩
    refine ⟨(8*c) • normalized,?_,?_⟩
    · change (8*c)*normalized.val first = 2*c ∧
        (8*c)*normalized.val second = -(2*c) ∧ (8*c)*normalized.val third = c
      rw [normalized_first,normalized_second,normalized_third]
      constructor
      · ring
      constructor <;> ring
    · intro F hF
      apply equivalence.injective
      have hc := hF.2.2
      rw [third_value] at hc
      rw [map_smul,show equivalence normalized = 1 from normalized_value]
      simp only [smul_eq_mul,mul_one]
      linear_combination 8*hc

theorem independent_values_rejected :
    ¬∃ F : selected.Coefficient,
      F.val first = 1 ∧ F.val second = 0 ∧ F.val third = 0 := by
  rintro ⟨F,h1,_,h3⟩
  rw [first_value] at h1
  rw [third_value] at h3
  have h : (1:ℂ) = 0 := by linear_combination -h1+2*h3
  exact one_ne_zero h

end
end Physics.ScalarQuarticLiteratureChecks
