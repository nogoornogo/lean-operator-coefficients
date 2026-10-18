import Math.RepresentationTheory.Characters.VirtualRepresentation
import GUT.SU6.Characters.NormalizedLaurent

open Math

/-!
# Restriction to a physical subgroup

This file isolates the final forward implication needed to pass from equality
in a target representation ring to equality of characters on the embedded
flipped torus.  For an arbitrary group homomorphism `G -> SU(6)`, restriction
is constructed by composing actual representations with that homomorphism.

No injectivity or character-separation theorem is used.  The remaining
model-specific work is to instantiate `G`, provide the torus lift, construct
the physical virtual target, and compute its torus character.
-/

namespace GUT
namespace PhysicalRestrictionBridge

open Math.PhysicalRestrictionBridge

open VirtualRestriction

noncomputable section

universe u

abbrev SU6 := ActualRestriction.SU6
abbrev EmbeddedFlippedTorus := FlippedTorus.FlippedDiagonalSU6Point
abbrev ActualSU6Representation := VirtualRestriction.ActualSU6Representation
abbrev FiniteVirtualSU6Representation :=
  VirtualRestriction.FiniteVirtualSU6Representation

/-- Restrict an actual `SU(6)` representation along `iota : G -> SU(6)`. -/
def restrictActual {G : Type u} [Group G] (iota : G →* SU6)
    (R : ActualSU6Representation) : ActualGroupRepresentation G where
  V := R.V
  instAddCommGroup := R.instAddCommGroup
  instModule := R.instModule
  instFiniteDimensional := R.instFiniteDimensional
  rho := R.rho.comp iota

def restrictSummand {G : Type u} [Group G] (iota : G →* SU6)
    (s : VirtualRestriction.VirtualSummand) : VirtualGroupSummand G where
  coeff := s.coeff
  rep := restrictActual iota s.rep

/-- Restriction of a finite virtual `SU(6)` representation, summand by summand. -/
def restrictVirtual {G : Type u} [Group G] (iota : G →* SU6) :
    FiniteVirtualSU6Representation -> FiniteVirtualGroupRepresentation G
  | [] => []
  | s :: ss => restrictSummand iota s :: restrictVirtual iota ss

/--
A pointwise lift of the already constructed flipped torus through a proposed
physical subgroup homomorphism.
-/
structure FlippedTorusLift {G : Type u} [Group G] (iota : G →* SU6) where
  point : EmbeddedFlippedTorus -> G
  maps_to : ∀ t, iota (point t) = t.toDiagonal.toSU6

theorem restrictActual_character_on_torus
    {G : Type u} [Group G] {iota : G →* SU6}
    (L : FlippedTorusLift iota) (R : ActualSU6Representation)
    (t : EmbeddedFlippedTorus) :
    (restrictActual iota R).character (L.point t) =
      R.restrictedCharacter t := by
  calc
    (restrictActual iota R).character (L.point t) =
        R.rho.character (iota (L.point t)) := rfl
    _ = R.rho.character t.toDiagonal.toSU6 := by rw [L.maps_to]
    _ = R.restrictedCharacter t := rfl

/-- Character formation commutes with finite virtual restriction on the torus. -/
theorem restrictVirtual_character_on_torus
    {G : Type u} [Group G] {iota : G →* SU6}
    (L : FlippedTorusLift iota)
    (chi : FiniteVirtualSU6Representation) (t : EmbeddedFlippedTorus) :
    FiniteVirtualGroupRepresentation.character (restrictVirtual iota chi)
        (L.point t) =
      FiniteVirtualSU6Representation.restrictedCharacter chi t := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp [restrictVirtual, FiniteVirtualGroupRepresentation.character,
        VirtualGroupSummand.character, restrictSummand,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        VirtualRestriction.VirtualSummand.restrictedCharacter,
        restrictActual_character_on_torus L s.rep t, ih]

/--
Any target whose torus character is represented by a non-`swap36`-fixed
Laurent polynomial is not character-equivalent to a restricted finite virtual
`SU(6)` representation.
-/
theorem no_characterEquivalent_restriction_of_not_swap36_fixed
    {G : Type u} [Group G] {iota : G →* SU6}
    (L : FlippedTorusLift iota)
    (target : FiniteVirtualGroupRepresentation G)
    (p : Flipped.Normalized.Poly)
    (hp : Flipped.Normalized.swap36 p ≠ p)
    (htarget : ∀ t,
      FiniteVirtualGroupRepresentation.character target (L.point t) =
        NormalizedVirtualRestriction.diagonalLaurentEval p t) :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      FiniteVirtualGroupRepresentation.CharacterEquivalent
        (restrictVirtual iota chi) target := by
  intro h
  rcases h with ⟨chi, hchi⟩
  apply
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed
      p hp
  refine ⟨chi, ?_⟩
  intro t
  calc
    FiniteVirtualSU6Representation.restrictedCharacter chi t =
        FiniteVirtualGroupRepresentation.character (restrictVirtual iota chi)
          (L.point t) := (restrictVirtual_character_on_torus L chi t).symm
    _ = FiniteVirtualGroupRepresentation.character target (L.point t) :=
      hchi (L.point t)
    _ = NormalizedVirtualRestriction.diagonalLaurentEval p t := htarget t

/-- The physical one-generation specialization of the forward bridge. -/
theorem no_flippedSMTarget_characterEquivalent_restriction
    {G : Type u} [Group G] {iota : G →* SU6}
    (L : FlippedTorusLift iota)
    (target : FiniteVirtualGroupRepresentation G)
    (htarget : ∀ t,
      FiniteVirtualGroupRepresentation.character target (L.point t) =
        NormalizedVirtualRestriction.diagonalLaurentEval
          Flipped.Normalized.flippedSMCharacter t) :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      FiniteVirtualGroupRepresentation.CharacterEquivalent
        (restrictVirtual iota chi) target :=
  no_characterEquivalent_restriction_of_not_swap36_fixed L target
    Flipped.Normalized.flippedSMCharacter
    Flipped.Normalized.swap36_flippedSMCharacter_ne htarget

/-- Character-function image form of the physical one-generation bridge. -/
theorem flippedSMTarget_character_not_mem_restrictionImage
    {G : Type u} [Group G] {iota : G →* SU6}
    (L : FlippedTorusLift iota)
    (target : FiniteVirtualGroupRepresentation G)
    (htarget : ∀ t,
      FiniteVirtualGroupRepresentation.character target (L.point t) =
        NormalizedVirtualRestriction.diagonalLaurentEval
          Flipped.Normalized.flippedSMCharacter t) :
    FiniteVirtualGroupRepresentation.character target ∉
      Set.range (fun chi : FiniteVirtualSU6Representation =>
        FiniteVirtualGroupRepresentation.character (restrictVirtual iota chi)) := by
  intro h
  rcases h with ⟨chi, hchi⟩
  apply no_flippedSMTarget_characterEquivalent_restriction L target htarget
  exact ⟨chi, fun g => congrFun hchi g⟩

end

end PhysicalRestrictionBridge
end GUT
