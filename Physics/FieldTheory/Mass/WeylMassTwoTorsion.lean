import Physics.FieldTheory.Mass.InvariantWeylMass
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.GroupWithZero.Units.Fintype

open Math

/-!
# A self-dual, nontrivially charged Majorana sector

The sign action of the two-element group `Int` units on one complex field
admits both zero mass and a nondegenerate symmetric mass. Their radicals
have different dimensions but the same dual chiral character. Thus the dual
index cannot recover self-dual sectors, including order-two residual charges.
This is a convention audit, not an SU(6) model or a counterexample to the scoped no-go theorem.
-/

set_option autoImplicit false

namespace GUT.WeylMassTwoTorsion

open InvariantWeylMass CompactEmbeddingClassification

noncomputable section

def signRepresentation : Representation ℂ ℤˣ ℂ where
  toFun u := ((u : ℤ) : ℂ) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    simp
  map_mul' u v := by
    apply LinearMap.ext
    intro z
    simp [mul_assoc, mul_comm]

@[simp]
theorem signRepresentation_apply (u : ℤˣ) (z : ℂ) :
    signRepresentation u z = ((u : ℤ) : ℂ) * z := rfl

theorem signRepresentation_unitary : IsUnitaryRepresentation signRepresentation := by
  intro u x y
  obtain rfl | rfl := Int.units_eq_one_or u <;> simp

theorem signRepresentation_nontrivial : signRepresentation (-1) (1 : ℂ) ≠ 1 := by
  norm_num

theorem signGroup_card : Fintype.card ℤˣ = 2 := Fintype.card_units_int

/-- A single sign-charged Weyl field has an allowed Majorana coefficient. -/
def majoranaMass : SymmetricMass signRepresentation where
  form := LinearMap.mul ℂ ℂ
  symmetric := ⟨mul_comm⟩
  invariant u x y := by
    obtain rfl | rfl := Int.units_eq_one_or u <;> simp

theorem majoranaMass_nondegenerate : majoranaMass.form.Nondegenerate := by
  constructor
  · intro x hx
    simpa [majoranaMass] using hx 1
  · intro y hy
    simpa [majoranaMass] using hy 1

theorem zero_mass_radical_finrank :
    Module.finrank ℂ (SymmetricMass.zero signRepresentation).radical.toSubmodule = 1 := by
  rw [SymmetricMass.radical_zero]
  simp

theorem majoranaMass_radical_finrank :
    Module.finrank ℂ majoranaMass.radical.toSubmodule = 0 := by
  rw [majoranaMass.radical_eq_bot_of_nondegenerate majoranaMass_nondegenerate]
  simp

theorem sign_dual_character_zero (u : ℤˣ) :
    signRepresentation.character u - signRepresentation.dual.character u = 0 := by
  rw [Representation.char_dual]
  obtain rfl | rfl := Int.units_eq_one_or u <;> simp

/-- The dual difference is zero even when the charged field is massless. -/
theorem radical_dual_character_zero (B : SymmetricMass signRepresentation) (u : ℤˣ) :
    B.radical.toRepresentation.character u - B.radical.toRepresentation.dual.character u = 0 := by
  rw [radical_dual_character_eq B signRepresentation_unitary, sign_dual_character_zero]

/-- Equality of dual chiral characters does not imply equality of the actual
light spectra, already for a nontrivial order-two residual action. -/
theorem same_dual_index_different_zero_modes :
    ∃ B C : SymmetricMass signRepresentation,
      (∀ u, B.radical.toRepresentation.character u -
          B.radical.toRepresentation.dual.character u =
        C.radical.toRepresentation.character u -
          C.radical.toRepresentation.dual.character u) ∧
      Module.finrank ℂ B.radical.toSubmodule ≠ Module.finrank ℂ C.radical.toSubmodule := by
  refine ⟨SymmetricMass.zero signRepresentation, majoranaMass, ?_, ?_⟩
  · intro u
    rw [radical_dual_character_zero, radical_dual_character_zero]
  · rw [zero_mass_radical_finrank, majoranaMass_radical_finrank]
    decide

end

end GUT.WeylMassTwoTorsion
