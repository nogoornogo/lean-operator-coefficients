import Math.RepresentationTheory.TripleSymmetricCoordinates
import Math.RepresentationTheory.TripleAlternatingCoordinates

/-! Nonredundant finite indices for all three qqql flavor symmetry types. -/
namespace Math.TripleFlavorCoordinates
set_option autoImplicit false
noncomputable section
abbrev Index (n : ℕ) := TripleSymmetricCoordinates.Index n ⊕
  (TripleAlternatingCoordinates.Index n ⊕ TripleMixedCoordinates.Index n)
abbrev Coordinates (n : ℕ) := Index n → ℂ
abbrev Space (n : ℕ) := TripleSymmetricCoordinates.space n ×
  (TripleAlternatingCoordinates.space n × TripleMixedCoordinates.space n)

def equiv (n : ℕ) : Space n ≃ₗ[ℂ] Coordinates n :=
  (LinearEquiv.prodCongr (TripleSymmetricCoordinates.equiv n)
    (LinearEquiv.prodCongr (TripleAlternatingCoordinates.equiv n)
      (TripleMixedCoordinates.equiv n))).trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl ℂ _)
      (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm)

theorem finrank_eq_index_card (n : ℕ) :
    Module.finrank ℂ (Space n) = Fintype.card (Index n) := by
  rw [(equiv n).finrank_eq, Module.finrank_fintype_fun_eq_card]

theorem index_card_zero : Fintype.card (Index 0) = 0 := by decide +kernel
theorem index_card_one : Fintype.card (Index 1) = 1 := by decide +kernel
theorem index_card_two : Fintype.card (Index 2) = 6 := by decide +kernel
theorem index_card_three : Fintype.card (Index 3) = 19 := by decide +kernel

/-- Lepton flavor is an independent finite slot; no conjugate doubling. -/
theorem three_generation_card : Fintype.card (Fin 3 × Index 3) = 57 := by
  rw [Fintype.card_prod, Fintype.card_fin, index_card_three]

end
end Math.TripleFlavorCoordinates
