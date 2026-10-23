import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalUpper

/-! One bounded finite field-coordinate classification. -/
namespace Physics.HiggsQuarticFourInternalUpper
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls
variable (f : A →ₗ[ℂ] ℂ)
  (hInternal : ∀ g p, p ∈ HiggsQuarticFourInput.V → f (T g p) = f p)

include hInternal in
theorem K_zero0 (hS : ∀ i : Fin 7, f (seven i) = 0) (j k l : Fin 4) :
    f (K 0 j k l) = 0 := by
  fin_cases j <;> fin_cases k <;> fin_cases l
  · exact vanish f hInternal 0 0 0 0 (by decide +kernel)
  · exact vanish f hInternal 0 0 0 1 (by decide +kernel)
  · exact vanish f hInternal 0 0 0 2 (by decide +kernel)
  · exact vanish f hInternal 0 0 0 3 (by decide +kernel)
  · exact vanish f hInternal 0 0 1 0 (by decide +kernel)
  · exact vanish f hInternal 0 0 1 1 (by decide +kernel)
  · exact vanish f hInternal 0 0 1 2 (by decide +kernel)
  · exact vanish f hInternal 0 0 1 3 (by decide +kernel)
  · exact vanish f hInternal 0 0 2 0 (by decide +kernel)
  · exact vanish f hInternal 0 0 2 1 (by decide +kernel)
  · exact hS 0
  · exact vanish f hInternal 0 0 2 3 (by decide +kernel)
  · exact vanish f hInternal 0 0 3 0 (by decide +kernel)
  · exact vanish f hInternal 0 0 3 1 (by decide +kernel)
  · exact vanish f hInternal 0 0 3 2 (by decide +kernel)
  · exact vanish f hInternal 0 0 3 3 (by decide +kernel)
  · exact vanish f hInternal 0 1 0 0 (by decide +kernel)
  · exact vanish f hInternal 0 1 0 1 (by decide +kernel)
  · exact vanish f hInternal 0 1 0 2 (by decide +kernel)
  · exact vanish f hInternal 0 1 0 3 (by decide +kernel)
  · exact vanish f hInternal 0 1 1 0 (by decide +kernel)
  · exact vanish f hInternal 0 1 1 1 (by decide +kernel)
  · exact vanish f hInternal 0 1 1 2 (by decide +kernel)
  · exact vanish f hInternal 0 1 1 3 (by decide +kernel)
  · exact vanish f hInternal 0 1 2 0 (by decide +kernel)
  · exact vanish f hInternal 0 1 2 1 (by decide +kernel)
  · exact vanish f hInternal 0 1 2 2 (by decide +kernel)
  · exact hS 1
  · exact vanish f hInternal 0 1 3 0 (by decide +kernel)
  · exact vanish f hInternal 0 1 3 1 (by decide +kernel)
  · exact (congrArg f (K_right 0 1 3 2)).trans (hS 1)
  · exact vanish f hInternal 0 1 3 3 (by decide +kernel)
  · exact vanish f hInternal 0 2 0 0 (by decide +kernel)
  · exact vanish f hInternal 0 2 0 1 (by decide +kernel)
  · exact hS 3
  · exact vanish f hInternal 0 2 0 3 (by decide +kernel)
  · exact vanish f hInternal 0 2 1 0 (by decide +kernel)
  · exact vanish f hInternal 0 2 1 1 (by decide +kernel)
  · exact vanish f hInternal 0 2 1 2 (by decide +kernel)
  · exact hS 4
  · exact (congrArg f (K_right 0 2 2 0)).trans (hS 3)
  · exact vanish f hInternal 0 2 2 1 (by decide +kernel)
  · exact vanish f hInternal 0 2 2 2 (by decide +kernel)
  · exact vanish f hInternal 0 2 2 3 (by decide +kernel)
  · exact vanish f hInternal 0 2 3 0 (by decide +kernel)
  · exact (congrArg f (K_right 0 2 3 1)).trans (hS 4)
  · exact vanish f hInternal 0 2 3 2 (by decide +kernel)
  · exact vanish f hInternal 0 2 3 3 (by decide +kernel)
  · exact vanish f hInternal 0 3 0 0 (by decide +kernel)
  · exact vanish f hInternal 0 3 0 1 (by decide +kernel)
  · exact vanish f hInternal 0 3 0 2 (by decide +kernel)
  · exact vanish f hInternal 0 3 0 3 (by decide +kernel)
  · exact vanish f hInternal 0 3 1 0 (by decide +kernel)
  · exact vanish f hInternal 0 3 1 1 (by decide +kernel)
  · exact hS 6
  · exact vanish f hInternal 0 3 1 3 (by decide +kernel)
  · exact vanish f hInternal 0 3 2 0 (by decide +kernel)
  · exact (congrArg f (K_right 0 3 2 1)).trans (hS 6)
  · exact vanish f hInternal 0 3 2 2 (by decide +kernel)
  · exact vanish f hInternal 0 3 2 3 (by decide +kernel)
  · exact vanish f hInternal 0 3 3 0 (by decide +kernel)
  · exact vanish f hInternal 0 3 3 1 (by decide +kernel)
  · exact vanish f hInternal 0 3 3 2 (by decide +kernel)
  · exact vanish f hInternal 0 3 3 3 (by decide +kernel)

end
end Physics.HiggsQuarticFourInternalUpper
