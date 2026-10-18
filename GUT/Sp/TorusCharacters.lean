import Math.LieGroups.Symplectic.Torus
import Physics.FieldTheory.Mass.SelfDualMassIndex

open Math

/-! Actual symplectic torus inversion forces zero dual character, including
after an invariant symmetric mass. No source self-duality certificate is
assumed. This does not assert conjugacy for arbitrary group elements. -/

set_option autoImplicit false

namespace GUT.CompactSymplectic

open Math.CompactSymplectic
noncomputable section

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ (Group n) V)

theorem torus_character_eq_dual (z : Torus n) :
    Representation.character (rho.comp (torusHom n)) z =
      Representation.character (Representation.dual (rho.comp (torusHom n))) z :=
  SelfDualCharacter.restrict_character_eq_dual_of_inversion_element rho
    (torusHom n) (inversionElement n) torusHom_inverse_conjugate z

theorem torus_mass_zero_index
    (B : InvariantWeylMass.SymmetricMass (rho.comp (torusHom n))) (z : Torus n) :
    B.radical.toRepresentation.character z -
      B.radical.toRepresentation.dual.character z = 0 :=
  B.radical_dual_character_zero_at z (torus_character_eq_dual rho z)

theorem torus_virtualCharacter_inv
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (reps : ∀ i, Representation ℂ (Group n) (W i)) (coeff : I →₀ ℤ) (z : Torus n) :
    CharacterRestriction.virtualCharacter reps coeff (torusHom n z⁻¹) =
      CharacterRestriction.virtualCharacter reps coeff (torusHom n z) :=
  SelfDualCharacter.virtualCharacter_restrict_inv reps coeff (torusHom n)
    (fun z => ⟨inversionElement n, torusHom_inverse_conjugate z⟩) z

end

end GUT.CompactSymplectic
