import Math.Algebra.Waves.HiggsFourWaveCubature
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourCoordinateAssembly

/-! Complete coefficients on the entire free, gaugeless Higgs grade (4,4).
The finite moments are proved here, not assumptions on the caller. -/
namespace Physics.HiggsQuarticFourCompleteness
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInput

theorem moments (r : Fin 3) : HiggsQuarticFourMomentInvariance.Moments r :=
  HiggsFourWaveCubature.moments r

def equivalence : selected.Coefficient ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  HiggsQuarticFourCoordinateAssembly.equivalence moments
def reconstruction : (Fin 3 → ℂ) →ₗ[ℂ] selected.Coefficient :=
  HiggsQuarticFourCoordinateAssembly.reconstruction moments
def normalized (i : Fin 3) : selected.Coefficient :=
  HiggsQuarticFourCoordinateAssembly.normalized moments i

theorem extraction (F : selected.Coefficient) (i : Fin 3) :
    equivalence F i = F.val (representatives i) := rfl
theorem normalized_value (i j : Fin 3) :
    equivalence (normalized i) j = if i = j then 1 else 0 :=
  HiggsQuarticFourCoordinateAssembly.normalized_value moments i j
theorem reconstruct (F : selected.Coefficient) : reconstruction (equivalence F) = F :=
  equivalence.symm_apply_apply F
theorem extract_reconstruction (c : Fin 3 → ℂ) : equivalence (reconstruction c) = c :=
  equivalence.apply_symm_apply c
theorem coefficient_dimension : Module.finrank ℂ selected.Coefficient = 3 :=
  HiggsQuarticFourCoordinateAssembly.coefficient_dimension moments

abbrev directSelected := HiggsQuarticFourCoordinateAssembly.directSelected
def inputEquivalence : selected.Coefficient ≃ₗ[ℂ] directSelected.Coefficient :=
  HiggsQuarticFourCoordinateAssembly.inputEquivalence
def directEquivalence : directSelected.Coefficient ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  HiggsQuarticFourCoordinateAssembly.directEquivalence moments
theorem direct_extraction (F : directSelected.Coefficient) (i : Fin 3) :
    directEquivalence F i = F.val (representatives i) := rfl
theorem input_agreement (F : selected.Coefficient) :
    directEquivalence (inputEquivalence F) = equivalence F := rfl

end
end Physics.HiggsQuarticFourCompleteness
