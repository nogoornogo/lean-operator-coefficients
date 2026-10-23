import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourCompleteness
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiInput

/-! Existing and new paper-density consumers of the entire admitted space.
Only their free, gaugeless ordinary-derivative specialization is asserted. -/
namespace Physics.HiggsQuarticFourLiterature
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInput

def murphyEquivalence := HiggsQuarticFourCompleteness.equivalence
theorem murphy_extraction (F : selected.Coefficient) (i : Fin 3) :
    murphyEquivalence F i = F.val (representatives i) := rfl

def liEquivalence : selected.Coefficient ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  HiggsQuarticFourCompleteness.equivalence.trans HiggsQuarticFourLiInput.coordinate
theorem li_extraction (F : selected.Coefficient) (i : Fin 3) :
    liEquivalence F i = F.val (HiggsQuarticFourLiInput.native i) :=
  (congrFun (HiggsQuarticFourLiInput.coefficient_values F) i).symm

def eboliOrder : Fin 3 → Fin 3 := ![1,2,0]
def eboliNative (i : Fin 3) : V := representatives (eboliOrder i)
def eboliCoordinate : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun c := ![c 1,c 2,c 0]
  invFun c := ![c 2,c 0,c 1]
  left_inv _ := by funext i; fin_cases i <;> rfl
  right_inv _ := by funext i; fin_cases i <;> rfl
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl
theorem eboli_coordinate_apply (c : Fin 3 → ℂ) (i : Fin 3) :
    eboliCoordinate c i = c (eboliOrder i) := by fin_cases i <;> rfl
def eboliEquivalence : selected.Coefficient ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  HiggsQuarticFourCompleteness.equivalence.trans eboliCoordinate
theorem eboli_extraction (F : selected.Coefficient) (i : Fin 3) :
    eboliEquivalence F i = F.val (eboliNative i) :=
  (eboli_coordinate_apply (HiggsQuarticFourCompleteness.equivalence F) i).trans
    (HiggsQuarticFourCompleteness.extraction F (eboliOrder i))

/-- Omitting O_S,2 loses an admitted nonzero coefficient. -/
theorem omitted_S2 : ∃ F : selected.Coefficient,
    F ≠ 0 ∧ F.val (eboliNative 0) = 0 ∧ F.val (eboliNative 1) = 0 ∧
      F.val (eboliNative 2) = 1 := by
  obtain ⟨F,hF⟩ := HiggsQuarticFourCompleteness.equivalence.surjective ![1,0,0]
  have hv (i : Fin 3) : F.val (representatives i) = (![1,0,0] : Fin 3 → ℂ) i :=
    (HiggsQuarticFourCompleteness.extraction F i).symm.trans (congrFun hF i)
  refine ⟨F,?_,hv 1,hv 2,hv 0⟩
  · intro hz
    have he := hv 0
    rw [hz] at he
    change (0:ℂ) = 1 at he
    exact zero_ne_one he

end
end Physics.HiggsQuarticFourLiterature
