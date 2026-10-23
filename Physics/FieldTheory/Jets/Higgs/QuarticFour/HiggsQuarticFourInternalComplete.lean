import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero0
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero1
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero2
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero3

/-! All field labels are controlled by the three Higgs contractions. -/
namespace Physics.HiggsQuarticFourInternalUpper
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls
variable (f : A →ₗ[ℂ] ℂ)
  (hInternal : ∀ g p, p ∈ HiggsQuarticFourInput.V → f (T g p) = f p)

include hInternal in
theorem K_zero (h1 : f q1 = 0) (h2 : f q2 = 0) (h3 : f q3 = 0) (i j k l : Fin 4) :
    f (K i j k l) = 0 := by
  have hs := seven_zero f hInternal h1 h2 h3
  fin_cases i
  · exact K_zero0 f hInternal hs j k l
  · exact K_zero1 f hInternal hs j k l
  · exact K_zero2 f hInternal hs j k l
  · exact K_zero3 f hInternal hs j k l

include hInternal in
theorem all_pairs_zero (h1 : f q1 = 0) (h2 : f q2 = 0) (h3 : f q3 = 0) (a b c d : Label) :
    f (pair (h a.1 a.2) (h b.1 b.2)*pair (h c.1 c.2) (h d.1 d.2)) = 0 := by
  obtain ⟨i,rfl⟩ := label_surjective a
  obtain ⟨j,rfl⟩ := label_surjective b
  obtain ⟨k,rfl⟩ := label_surjective c
  obtain ⟨l,rfl⟩ := label_surjective d
  exact K_zero f hInternal h1 h2 h3 i j k l

end
end Physics.HiggsQuarticFourInternalUpper
