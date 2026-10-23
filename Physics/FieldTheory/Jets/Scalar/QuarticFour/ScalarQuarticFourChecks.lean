import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourCompleteness
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarCompletenessChecks

/-! Actual-input extraction and controls separating invariant coefficients
from the much larger un-invariant quotient. -/
namespace Physics.ScalarQuarticFourChecks
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM ScalarQuarticFourTensors
open ScalarQuarticFourCompleteness ScalarQuarticContractions LorentzFiniteControls

def quotientFunctional : P.Source →ₗ[ℂ] ℂ := P.relations.liftQ functional annihilates
@[simp] theorem quotient_evaluation (p : OffShell) : quotientFunctional (q p) = functional p := rfl

theorem A_value : functional A = 1 := by
  have he := congrArg quotientFunctional A_eq_C4
  simpa only [quotient_evaluation,normalization] using he

theorem B_value : functional B = (-1/2 : ℂ) := by
  have he := congrArg quotientFunctional B_eq_C4
  simpa only [map_smul,quotient_evaluation,normalization,smul_eq_mul,mul_one] using he

theorem Cao_value : functional ScalarCompletenessChecks.Cao.combination = (3/2 : ℂ) := by
  have he := congrArg quotientFunctional ScalarCompletenessChecks.Cao.quotient_normalization
  simpa only [map_smul,quotient_evaluation,normalization,smul_eq_mul,mul_one] using he

theorem restriction_coordinate (F : P.Coefficient) :
    equivalence (P.restrict V stable F) = F.val C4 := rfl

theorem restriction_reconstruction (F : P.Coefficient) :
    P.restrict V stable F = (F.val C4) • normalized :=
  (reconstruction (P.restrict V stable F)).symm

theorem quotient_extraction (F : selected.Coefficient) (p : V) :
    selected.coefficientEquiv F (selected.projection p) = F.val p := rfl

theorem normalized_extraction :
    selected.coefficientEquiv normalized (selected.projection ScalarQuarticFourUpper.generator) = 1 :=
  normalized_value

def probe : OffShell := (D 0 field)^4

theorem probe_word : probe = word 4 (E 0) (E 0) (E 0) (E 0) := by
  simp only [probe,word,j1,E,dirD_single,one_smul]
  ring

theorem probe_grade : probe ∈ V := by
  rw [probe_word]
  exact word_grade _ _ _ _ _

theorem probe_value : functional probe = (1/8 : ℂ) := by
  rw [probe_word,← tensor_apply,basis_formula]
  norm_num [alpha,beta,ScalarFourWaveCubature.alpha,ScalarFourWaveCubature.beta,LorentzRankFour.metric]

theorem probe_transformed_value (g : LorentzDirections.Group) :
    functional (offAction g probe) = (1/8 : ℂ) :=
  (invariant g ⟨probe,probe_grade⟩).trans probe_value

/-- The anisotropic class is not in the invariant representative line. -/
theorem probe_not_in_candidate_image : q probe ∉ candidateImage := by
  rw [candidate_image_eq]
  intro hp
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hp
  have hn := congrArg quotientFunctional hc
  have hsep := congrArg
    (P.relations.liftQ ScalarQuarticFourWitness.separator ScalarQuarticFourWitness.annihilates) hc
  simp only [map_smul,quotient_evaluation,normalization,probe_value,smul_eq_mul,mul_one] at hn
  rw [map_smul] at hsep
  change c • ScalarQuarticFourWitness.separator C4 = ScalarQuarticFourWitness.separator probe at hsep
  rw [hn,ScalarQuarticFourWitness.four_value] at hsep
  change (1/8 : ℂ) • (48 : ℂ) = ScalarQuarticFourWitness.separator ((D 0 field)^4) at hsep
  rw [ScalarQuarticFourWitness.separator_before] at hsep
  norm_num at hsep

theorem coefficient_scope_control :
    Module.finrank ℂ selected.Coefficient = 1 ∧ q probe ∉ candidateImage :=
  ⟨coefficient_dimension,probe_not_in_candidate_image⟩

end
end Physics.ScalarQuarticFourChecks
