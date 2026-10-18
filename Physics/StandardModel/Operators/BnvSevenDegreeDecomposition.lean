import Physics.StandardModel.Operators.BnvMixedInput

/-! The independent bounded dimension-seven input splits by its two possible
engineering degrees. This is a degree decomposition, not the family/Hom endpoint. -/
namespace GUT.BnvSevenDegreeDecomposition
set_option autoImplicit false
noncomputable section
open Representation BnvMixedInput DeltaLOneSignedInput

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

abbrev DegreeProduct := bnvSector flavor scalarFlavor 4 0 × bnvSector flavor scalarFlavor 4 1

def assemble (c : DegreeProduct flavor scalarFlavor) : bounded flavor scalarFlavor 7 :=
  ⟨Pi.single (4, 0) c.1 + Pi.single (4, 1) c.2, by
    intro nm hd
    have h0 : nm ≠ (4, 0) := by intro he; subst nm; norm_num at hd
    have h1 : nm ≠ (4, 1) := by intro he; subst nm; norm_num at hd
    simp [h0, h1]⟩

theorem outside (f : bounded flavor scalarFlavor 7) (nm : Fin 8 × Fin 12)
    (h0 : nm ≠ (4, 0)) (h1 : nm ≠ (4, 1)) : f.val nm = 0 := by
  by_cases hd : 14 < 3 * nm.1.val + 2 * nm.2.val
  · exact f.property nm hd
  · apply bnv_eq_zero_outside_seven_degrees flavor scalarFlavor _ (by omega)
    have hn0 : ¬ (nm.1.val = 4 ∧ nm.2.val = 0) := by
      rintro ⟨ha, hb⟩
      apply h0
      apply Prod.ext <;> apply Fin.ext <;> assumption
    have hn1 : ¬ (nm.1.val = 4 ∧ nm.2.val = 1) := by
      rintro ⟨ha, hb⟩
      apply h1
      apply Prod.ext <;> apply Fin.ext <;> assumption
    omega

def equiv : bounded flavor scalarFlavor 7 ≃ₗ[ℂ] DegreeProduct flavor scalarFlavor where
  toFun f := (f.val (4, 0), f.val (4, 1))
  invFun := assemble flavor scalarFlavor
  left_inv f := by
    apply Subtype.ext
    funext nm
    by_cases h0 : nm = (4, 0)
    · subst nm; simp [assemble]
    by_cases h1 : nm = (4, 1)
    · subst nm; simp [assemble]
    · simp [assemble, h0, h1, outside flavor scalarFlavor f nm h0 h1]
  right_inv c := by simp [assemble]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end GUT.BnvSevenDegreeDecomposition
