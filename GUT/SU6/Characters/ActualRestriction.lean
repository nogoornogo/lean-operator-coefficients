import GUT.SU6.SelectionRules.FlippedBranch.ConcreteBridge
import Math.RepresentationTheory.Decomposition.MathlibBridge
import Math.RepresentationTheory.Characters.CharacterRestriction

open Math

/-!
# Actual SU(6) restricted characters and the flipped Laurent model

This module packages the bridge from genuine finite-dimensional
`SU(6)` representations to the modeled `(3 6)` invariance.

The kernel-checked content here is:

* the restricted character of any finite-dimensional complex representation of
  `Matrix.specialUnitaryGroup (Fin 6) ℂ` is fixed under the concrete `(3 6)`
  Weyl action on diagonal torus points;
* any faithful Laurent-polynomial model of that restricted character, whose
  evaluation is compatible with the modeled `swap36`, is fixed by
  `Flipped.swap36`.

The finite-virtual closure step is handled in `GUT.VirtualRestriction`.
Actual summand polynomials from genuine torus character theory are needed when
one wants a Laurent polynomial for every source representation.  The later
function-level no-uplift theorem in `GUT.NormalizedLaurent` needs only the
character invariance proved here and a faithful Laurent model for the explicit
target, so it does not require that source-side polynomial construction.
-/

namespace GUT
namespace ActualRestriction

open Representation

noncomputable section

abbrev SU6 := MathlibBridge.SU6

structure DiagonalSU6Point where
  coords : WeylMatrix.I6 -> ℂ
  mem : Matrix.diagonal coords ∈ Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ

namespace DiagonalSU6Point

def toSU6 (t : DiagonalSU6Point) : SU6 :=
  ⟨Matrix.diagonal t.coords, t.mem⟩

def swap36 (t : DiagonalSU6Point) : DiagonalSU6Point where
  coords := t.coords ∘ WeylMatrix.swap36
  mem := by
    let g : SU6 := WeylMatrix.signedSwap36SU * t.toSU6 * WeylMatrix.signedSwap36SU⁻¹
    have hg : ((g : SU6) : Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ) =
        Matrix.diagonal (t.coords ∘ WeylMatrix.swap36) := by
      change
        ((WeylMatrix.signedSwap36SU : Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ) :
              Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ) *
            Matrix.diagonal t.coords *
            ((WeylMatrix.signedSwap36SU⁻¹ :
                Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ) :
              Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ) =
          Matrix.diagonal (t.coords ∘ WeylMatrix.swap36)
      exact WeylMatrix.signedSwap36SU_conj_diagonal t.coords
    rw [← hg]
    exact SetLike.coe_mem g

theorem toSU6_swap36_eq_conj (t : DiagonalSU6Point) :
    (swap36 t).toSU6 =
      WeylMatrix.signedSwap36SU * t.toSU6 * WeylMatrix.signedSwap36SU⁻¹ := by
  apply Subtype.ext
  change Matrix.diagonal (t.coords ∘ WeylMatrix.swap36) =
    ((WeylMatrix.signedSwap36SU : Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ) :
        Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ) *
      Matrix.diagonal t.coords *
      ((WeylMatrix.signedSwap36SU⁻¹ :
          Matrix.specialUnitaryGroup WeylMatrix.I6 ℂ) :
        Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ)
  exact (WeylMatrix.signedSwap36SU_conj_diagonal t.coords).symm

theorem ambientPoint_swap36 (t : DiagonalSU6Point) :
    ConcreteBridge.ambientPointOfDiag (swap36 t).coords =
      Flipped.AmbientPoint.swap36 (ConcreteBridge.ambientPointOfDiag t.coords) := by
  exact ConcreteBridge.ambientPointOfDiag_swap36 t.coords

end DiagonalSU6Point

def restrictedCharacter
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) (t : DiagonalSU6Point) : ℂ :=
  ρ.character t.toSU6

theorem restrictedCharacter_swap36_fixed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) (t : DiagonalSU6Point) :
    restrictedCharacter ρ (DiagonalSU6Point.swap36 t) = restrictedCharacter ρ t := by
  exact CharacterRestriction.character_restriction_invariant ρ
    DiagonalSU6Point.toSU6 DiagonalSU6Point.swap36 WeylMatrix.signedSwap36SU
    DiagonalSU6Point.toSU6_swap36_eq_conj t

def concreteWeylActionData :
    Flipped.WeylActionByConjugation SU6 DiagonalSU6Point where
  incl := DiagonalSU6Point.toSU6
  action := DiagonalSU6Point.swap36
  conjugateByRepresentative := fun g =>
    WeylMatrix.signedSwap36SU * g * WeylMatrix.signedSwap36SU⁻¹
  action_eq_conjugate := DiagonalSU6Point.toSU6_swap36_eq_conj

def representationFixedByConjugation
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) :
    Flipped.FixedByConjugation SU6 ℂ concreteWeylActionData.conjugateByRepresentative where
  toFun := ρ.character
  conjugation_fixed := by
    intro g
    exact MathlibBridge.su6_representation_character_conj ρ g WeylMatrix.signedSwap36SU

theorem restrictedCharacter_swap36_fixed_via_bridge
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) (t : DiagonalSU6Point) :
    Flipped.FixedByConjugation.restrictAlong concreteWeylActionData
        (representationFixedByConjugation ρ)
        (DiagonalSU6Point.swap36 t) =
      Flipped.FixedByConjugation.restrictAlong concreteWeylActionData
        (representationFixedByConjugation ρ)
        t := by
  exact Flipped.FixedByConjugation.restricted_fixed_by_weyl_action
    concreteWeylActionData (representationFixedByConjugation ρ) t

structure LaurentRestrictedCharacterModel
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) where
  poly : Flipped.Poly
  eval : Flipped.Poly -> DiagonalSU6Point -> ℂ
  evaluates_character : ∀ t, eval poly t = restrictedCharacter ρ t
  eval_swap36 :
    ∀ p t, eval (Flipped.swap36 p) t = eval p (DiagonalSU6Point.swap36 t)
  faithful :
    ∀ p q, (∀ t, eval p t = eval q t) -> p = q

namespace LaurentRestrictedCharacterModel

theorem swap36_fixed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ SU6 V}
    (M : LaurentRestrictedCharacterModel ρ) :
    Flipped.swap36 M.poly = M.poly := by
  apply M.faithful
  intro t
  rw [M.eval_swap36, M.evaluates_character, M.evaluates_character,
    restrictedCharacter_swap36_fixed]

theorem poly_ne_flippedSMCharacter
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ SU6 V}
    (M : LaurentRestrictedCharacterModel ρ) :
    M.poly ≠ Flipped.flippedSMCharacter := by
  intro h
  have hfixed := M.swap36_fixed
  rw [h] at hfixed
  exact Flipped.swap36_flippedSM_ne hfixed

theorem poly_ne_flippedSMCharacterExplicit
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ SU6 V}
    (M : LaurentRestrictedCharacterModel ρ) :
    M.poly ≠ Flipped.flippedSMCharacterExplicit := by
  intro h
  have hfixed := M.swap36_fixed
  rw [h] at hfixed
  exact Flipped.swap36_flippedSMExplicit_ne hfixed

end LaurentRestrictedCharacterModel

end

end ActualRestriction
end GUT
