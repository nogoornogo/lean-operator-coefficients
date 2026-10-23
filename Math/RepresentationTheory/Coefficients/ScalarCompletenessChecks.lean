import Math.RepresentationTheory.Coefficients.ScalarTwoSpeciesCompleteness

/-! Consumers of the finite C1 completeness results through the existing input API.
In particular, quotient-zero total derivatives are not closed under products. -/
namespace Math.ScalarCompletenessChecks
set_option autoImplicit false
noncomputable section
open TwoSpeciesDerivativeChecks ScalarTwoSpeciesCompleteness

def restrictFirst (r : Fin 2) (c : ℂ) :=
  input.restrict (source r.val 1) (fun _ => le_refl _) (c • firstGlobal r)
def restrictSecond (c : ℂ) :=
  input.restrict (source 1 2) (fun _ => le_refl _) (c • secondGlobal)

theorem first_restriction (r : Fin 2) (c : ℂ) :
    restrictFirst r c = (firstEquiv r).symm c := by
  apply (firstEquiv r).injective
  rw [LinearEquiv.apply_symm_apply]
  exact first_global_value r c

theorem second_restriction (c : ℂ) : restrictSecond c = secondEquiv.symm c := by
  apply secondEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact second_global_value c

theorem first_selected_evaluation (r : Fin 2) (c : ℂ) (p : source r.val 1) :
    (Line.selected (source r.val 1)).coefficientEquiv (restrictFirst r c)
      ((Line.selected (source r.val 1)).projection p) = c*firstFunctional r.val p.val := rfl

theorem second_selected_evaluation (c : ℂ) (p : source 1 2) :
    (Line.selected (source 1 2)).coefficientEquiv (restrictSecond c)
      ((Line.selected (source 1 2)).projection p) = c*secondFunctional p.val := rfl

theorem first_image_evaluation (r : Fin 2) (p : source r.val 1) :
    firstImageEquiv r (input.selectionEquiv (source r.val 1) (fun _ => le_refl _)
      ((Line.selected (source r.val 1)).projection p)) = firstFunctional r.val p.val := rfl

theorem second_image_evaluation (p : source 1 2) :
    secondImageEquiv (input.selectionEquiv (source 1 2) (fun _ => le_refl _)
      ((Line.selected (source 1 2)).projection p)) = secondFunctional p.val := rfl

theorem first_transported (b : A ≃ₗ[ℂ] A) (r : Fin 2) (c : ℂ) :
    (InputPresentation.reexpress input b).coefficientEquiv
      (InputPresentation.reexpressCoefficients input b (c • firstGlobal r))
      ((InputPresentation.reexpress input b).projection (b (firstWord r.val))) = c :=
  (InputPresentation.reexpress_evaluation input b _ _).trans (first_global_value r c)

theorem second_transported (b : A ≃ₗ[ℂ] A) (c : ℂ) :
    (InputPresentation.reexpress input b).coefficientEquiv
      (InputPresentation.reexpressCoefficients input b (c • secondGlobal))
      ((InputPresentation.reexpress input b).projection (b secondWord)) = c :=
  (InputPresentation.reexpress_evaluation input b _ _).trans (second_global_value c)

theorem first_swap : swapSpecies (firstWord 0) = otherWord 0 := by
  simp [swapSpecies,firstWord,otherWord,first,field,ScalarJetAlgebra.shift]
  ring

theorem first_swap_sign : firstFunctional 0 (swapSpecies (firstWord 0)) = -1 := by
  rw [first_swap,other_value]

theorem second_swap : swapSpecies secondWord = secondWord := by
  simp [swapSpecies,secondWord,first,field,ScalarJetAlgebra.shift]
  ring

theorem second_swap_value : secondFunctional (swapSpecies secondWord) = 1 := by
  rw [second_swap,second_value]

theorem ibp_product_control : q (first 0) = 0 ∧ q (field 1*first 0) ≠ 0 := by
  constructor
  · exact derivative_zero (field 0)
  · simpa [firstWord,mul_comm] using first_nonzero (0 : Fin 2)

end
end Math.ScalarCompletenessChecks
