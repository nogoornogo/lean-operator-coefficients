import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.RepresentationTheory.Characters.SelfDualCharacter

open Math

/-!
# Zero light dual index from self-dual sources

The source condition is independent of the chosen invariant symmetric mass.
It does not imply that the radical vanishes or that every source admits a
nondegenerate symmetric mass. Only the tested subgroup must preserve mass.
-/

set_option autoImplicit false

namespace GUT.InvariantWeylMass.SymmetricMass

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {rho : Representation ℂ G V}

theorem radical_dual_character_zero_at (B : SymmetricMass rho) (g : G)
    (hsource : rho.character g = rho.dual.character g) :
    B.radical.toRepresentation.character g -
      B.radical.toRepresentation.dual.character g = 0 := by
  rw [B.radical_dual_character_eq, hsource, sub_self]

theorem radical_dual_character_zero_of_equiv (B : SymmetricMass rho)
    (e : Representation.Equiv rho rho.dual) (g : G) :
    B.radical.toRepresentation.character g -
      B.radical.toRepresentation.dual.character g = 0 :=
  B.radical_dual_character_zero_at g (congrFun (Representation.char_iso e) g)

variable {K : Type*} [Group K] (rho : Representation ℂ G V) (i : K →* G)

theorem restricted_radical_dual_character_zero_of_equiv
    (B : SymmetricMass (rho.comp i)) (e : Representation.Equiv rho rho.dual) (g : K) :
    B.radical.toRepresentation.character g -
      B.radical.toRepresentation.dual.character g = 0 :=
  B.radical_dual_character_zero_at g
    (SelfDualCharacter.restrict_character_eq_dual_of_equiv rho i e g)

theorem restricted_radical_dual_character_zero_of_conjugate_inverse
    (B : SymmetricMass (rho.comp i))
    (hconj : ∀ g, ∃ n : G, i g⁻¹ = n * i g * n⁻¹) (g : K) :
    B.radical.toRepresentation.character g -
      B.radical.toRepresentation.dual.character g = 0 :=
  B.radical_dual_character_zero_at g
    (SelfDualCharacter.restrict_character_eq_dual_of_conjugate_inverse rho i hconj g)

theorem restricted_radical_dual_character_zero_of_inversion_element
    (B : SymmetricMass (rho.comp i)) (n : G)
    (hconj : ∀ g, i g⁻¹ = n * i g * n⁻¹) (g : K) :
    B.radical.toRepresentation.character g -
      B.radical.toRepresentation.dual.character g = 0 :=
  restricted_radical_dual_character_zero_of_conjugate_inverse rho i B
    (fun g => ⟨n, hconj g⟩) g

end

end GUT.InvariantWeylMass.SymmetricMass
