import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveInvariant
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsUpper

/-! Complete actual-group coefficients on the whole free one-flavor C5
grade. All source, moment and full-relation obligations are discharged. -/
namespace Physics.WeylHiggsCompleteness
set_option autoImplicit false
noncomputable section
open Math WeylHiggsInput

def normalized : selected.Coefficient :=
  (384*Complex.I)⁻¹ • WeylHiggsWaveInvariant.coefficient

theorem normalized_value : WeylHiggsSelection.evaluate normalized = 1 := by
  rw [normalized,map_smul,WeylHiggsWaveInvariant.candidate_value,smul_eq_mul]
  apply inv_mul_cancel₀
  norm_num

def reconstruction : ℂ →ₗ[ℂ] selected.Coefficient where
  toFun c := c • normalized
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := (smul_smul _ _ _).symm

theorem evaluate_reconstruction (c : ℂ) :
    WeylHiggsSelection.evaluate (reconstruction c) = c := by
  change WeylHiggsSelection.evaluate (c • normalized) = c
  rw [map_smul,normalized_value,smul_eq_mul,mul_one]

def equivalence : selected.Coefficient ≃ₗ[ℂ] ℂ where
  toLinearMap := WeylHiggsSelection.evaluate
  invFun := reconstruction
  left_inv F := WeylHiggsUpper.evaluate_injective (evaluate_reconstruction (WeylHiggsSelection.evaluate F))
  right_inv := evaluate_reconstruction

theorem extraction (F : selected.Coefficient) :
    equivalence F = F.val WeylHiggsSelection.candidate := rfl
theorem reconstruct (F : selected.Coefficient) : reconstruction (equivalence F) = F :=
  equivalence.symm_apply_apply F
theorem extract_reconstruction (c : ℂ) : equivalence (reconstruction c) = c :=
  equivalence.apply_symm_apply c
theorem coefficient_dimension : Module.finrank ℂ selected.Coefficient = 1 := by
  rw [equivalence.finrank_eq]
  simp
theorem normalized_nonzero : normalized ≠ 0 := by
  intro h
  have hv := normalized_value
  rw [h,map_zero] at hv
  exact zero_ne_one hv

def generatedEquivalence : WeylHiggsSelection.generatedSelected.Coefficient ≃ₗ[ℂ] ℂ :=
  WeylHiggsSelection.selectedCoefficientEquiv.trans equivalence
theorem generated_extraction (F : WeylHiggsSelection.generatedSelected.Coefficient) :
    generatedEquivalence F = F.val WeylHiggsSelection.candidate := rfl
theorem input_agreement (F : WeylHiggsSelection.generatedSelected.Coefficient) :
    equivalence (WeylHiggsSelection.selectedCoefficientEquiv F) = generatedEquivalence F := rfl
theorem generated_dimension : Module.finrank ℂ WeylHiggsSelection.generatedSelected.Coefficient = 1 := by
  rw [generatedEquivalence.finrank_eq]
  simp

end
end Physics.WeylHiggsCompleteness
