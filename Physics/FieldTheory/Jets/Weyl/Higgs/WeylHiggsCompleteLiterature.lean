import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCompleteness
import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsLiterature

/-! Native Li/Murphy coordinates and DHM sign controls for the completed
free one-flavor coefficient input. No paper count is a proof premise. -/
namespace Physics.WeylHiggsCompleteLiterature
set_option autoImplicit false
noncomputable section
open Math PairedWeylKinetic WeylHiggsInput WeylHiggsCompleteness
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def li : V := WeylHiggsSelection.candidate
def murphy : V := WeylHiggsLiterature.murphySelected
theorem native_equal : murphy = li := Subtype.ext WeylHiggsLiterature.li_murphy

def liCoordinate : selected.Coefficient ≃ₗ[ℂ] ℂ := equivalence
def murphyCoordinate : selected.Coefficient ≃ₗ[ℂ] ℂ := equivalence
theorem li_extraction (F : selected.Coefficient) : liCoordinate F = F.val li := rfl
theorem murphy_extraction (F : selected.Coefficient) : murphyCoordinate F = F.val murphy := by
  rw [native_equal]
  rfl
theorem native_agreement (F : selected.Coefficient) : murphyCoordinate F = liCoordinate F := rfl
theorem li_roundtrip (F : selected.Coefficient) : liCoordinate.symm (liCoordinate F) = F :=
  liCoordinate.symm_apply_apply F
theorem li_inverse (c : ℂ) : liCoordinate (liCoordinate.symm c) = c := liCoordinate.apply_symm_apply c
theorem murphy_roundtrip (F : selected.Coefficient) : murphyCoordinate.symm (murphyCoordinate F) = F :=
  murphyCoordinate.symm_apply_apply F
theorem murphy_inverse (c : ℂ) : murphyCoordinate (murphyCoordinate.symm c) = c :=
  murphyCoordinate.apply_symm_apply c
theorem li_normalized : normalized.val li = 1 := normalized_value
theorem murphy_normalized : normalized.val murphy = 1 := by rw [native_equal]; exact li_normalized

theorem li_in_full_quotient_nonzero : input.projection li.val ≠ 0 := by
  intro h
  have hr : li.val ∈ input.relations := (Submodule.Quotient.mk_eq_zero _).mp h
  have hz : normalized.val li = 0 := normalized.property hr
  exact zero_ne_one (hz.symm.trans li_normalized)

def reversedDensity : A := Complex.I • ∑ i : Fin 4,
  MinkowskiWeylCurrent.reversedBar i (DerivativeLiteratureMixed.psi false)
    (DerivativeLiteratureMixed.psi true)*DerivativeLiteratureMixed.higgsCurrent i*DerivativeLiteratureMixed.rho
theorem reversal_density : reversedDensity = -li.val := by
  change _ = -DerivativeLiteratureMixed.candidate
  simp only [reversedDensity,DerivativeLiteratureMixed.candidate,WeylHiggsLiterature.dhm_reversal,
    neg_mul,Finset.sum_neg_distrib,smul_neg]
  simp only [neg_neg]
def reversed : V := ⟨reversedDensity,by rw [reversal_density]; exact V.neg_mem li.property⟩
theorem reversed_normalized : normalized.val reversed = -1 := by
  have he : reversed = -li := Subtype.ext reversal_density
  rw [he,map_neg,li_normalized]
theorem wrong_reversal_detected : normalized.val reversed ≠ normalized.val li := by
  rw [reversed_normalized,li_normalized]
  norm_num
theorem wrong_factor_detected : normalized.val ((2 : ℂ) • li) ≠ normalized.val li := by
  rw [map_smul,li_normalized,smul_eq_mul,mul_one]
  norm_num

def generatedNormalized : WeylHiggsSelection.generatedSelected.Coefficient :=
  WeylHiggsSelection.selectedCoefficientEquiv.symm normalized
theorem generated_native_values :
    generatedNormalized.val li = 1 ∧
      (WeylHiggsSelection.selectedCoefficientEquiv generatedNormalized).val murphy = 1 := by
  have ht : WeylHiggsSelection.selectedCoefficientEquiv generatedNormalized = normalized :=
    WeylHiggsSelection.selectedCoefficientEquiv.apply_symm_apply normalized
  constructor
  · rw [← WeylHiggsSelection.selected_extraction,ht]
    exact li_normalized
  · rw [ht]
    exact murphy_normalized

end
end Physics.WeylHiggsCompleteLiterature
