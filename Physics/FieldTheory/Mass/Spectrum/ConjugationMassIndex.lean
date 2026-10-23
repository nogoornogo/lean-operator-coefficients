import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex
import Math.RepresentationTheory.Characters.CharacterRestriction

open Math

/-!
# Conjugation invariance after removing invariant symmetric masses

The dual character difference of the radical inherits ambient conjugation
invariance, even when the mass and radical are not invariant under the
conjugator. The residual group need not be Abelian.
-/

set_option autoImplicit false

namespace Physics.ConjugationMassIndex

noncomputable section

open InvariantWeylMass

variable {G K V : Type*} [Group G] [Group K]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem radical_dual_character_invariant
    (j : K →* G) (a : K →* K) (n : G)
    (hc : ∀ x, j (a x) = n * j x * n⁻¹)
    (rho : Representation ℂ G V) (B : SymmetricMass (rho.comp j)) (x : K) :
    B.radical.toRepresentation.character (a x) -
        B.radical.toRepresentation.dual.character (a x) =
      B.radical.toRepresentation.character x -
        B.radical.toRepresentation.dual.character x := by
  rw [B.radical_dual_character_eq, B.radical_dual_character_eq]
  have hi (y : K) : Representation.character (rho.comp j) (a y) =
      Representation.character (rho.comp j) y :=
    CharacterRestriction.character_restriction_invariant rho j a n hc y
  have hd : (Representation.dual (rho.comp j)).character (a x) =
      (Representation.dual (rho.comp j)).character x := by
    rw [Representation.char_dual, Representation.char_dual, ← map_inv]
    exact hi x⁻¹
  rw [hi, hd]

/-- A commuting residual action is retained at every group element, not only
at the identity or after taking dimensions. No `CommGroup H` is required. -/
theorem radical_dual_character_invariant_prod
    {H T : Type*} [Group H] [Group T]
    (j : T →* G) (a : T →* T) (n : G)
    (hc : ∀ t, j (a t) = n * j t * n⁻¹)
    (rho : Representation ℂ (G × H) V)
    (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H)))) (t : T) (h : H) :
    B.radical.toRepresentation.character (a t, h) -
        B.radical.toRepresentation.dual.character (a t, h) =
      B.radical.toRepresentation.character (t, h) -
        B.radical.toRepresentation.dual.character (t, h) := by
  have hc' (x : T × H) :
      (j.prodMap (MonoidHom.id H)) ((a.prodMap (MonoidHom.id H)) x) =
        (n, 1) * (j.prodMap (MonoidHom.id H)) x * (n, 1)⁻¹ := by
    apply Prod.ext
    · exact hc x.1
    · simp
  exact radical_dual_character_invariant
    (j.prodMap (MonoidHom.id H)) (a.prodMap (MonoidHom.id H)) (n, 1) hc' rho B (t, h)

end

end Physics.ConjugationMassIndex
