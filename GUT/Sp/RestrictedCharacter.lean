import Math.LieGroups.Symplectic.TorusConjugacy
import Physics.FieldTheory.Mass.SelfDualMassIndex

open Math

/-! Every actual compact symplectic element is conjugate to its inverse.
Thus every subgroup restriction has zero source and mass-radical dual
character, with no assumed conjugacy or self-duality certificate. -/

set_option autoImplicit false

namespace GUT.CompactSymplectic

open Math.CompactSymplectic
noncomputable section

variable {n : ℕ} {K V : Type*} [_root_.Group K] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ (Group n) V)

theorem restriction_inverse_conjugate (i : K →* Group n) (k : K) :
    ∃ u : Group n, i k⁻¹ = u * i k * u⁻¹ := by
  rw [map_inv]
  exact inverse_conjugate (i k)

theorem restricted_character_eq_dual (i : K →* Group n) (k : K) :
    Representation.character (rho.comp i) k =
      Representation.character (Representation.dual (rho.comp i)) k :=
  SelfDualCharacter.restrict_character_eq_dual_of_conjugate_inverse rho i
    (restriction_inverse_conjugate i) k

theorem restricted_mass_zero_index (i : K →* Group n)
    (B : InvariantWeylMass.SymmetricMass (rho.comp i)) (k : K) :
    B.radical.toRepresentation.character k -
      B.radical.toRepresentation.dual.character k = 0 :=
  B.radical_dual_character_zero_at k (restricted_character_eq_dual rho i k)

theorem virtualCharacter_inv {I : Type*} {W : I → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] [∀ j, FiniteDimensional ℂ (W j)]
    (reps : ∀ j, Representation ℂ (Group n) (W j)) (coeff : I →₀ ℤ) (g : Group n) :
    CharacterRestriction.virtualCharacter reps coeff g⁻¹ =
      CharacterRestriction.virtualCharacter reps coeff g :=
  SelfDualCharacter.virtualCharacter_restrict_inv reps coeff (MonoidHom.id _)
    inverse_conjugate g

end

end GUT.CompactSymplectic
