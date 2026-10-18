import GUT.SU6.SelectionRules.FlippedBranch.FlippedSMTarget

open Math

/-!
# Quotients of finite virtual representations by character equality

The no-uplift argument only needs the additive virtual-representation data and
the forward map to characters.  This file therefore forms the precise quotient
of finite virtual representations by equality of their whole-group characters.
Restriction is well-defined on this quotient, and the concrete physical target
class is outside its image.

This quotient is deliberately named a virtual-character quotient rather than a
Grothendieck representation ring.  Identifying it with a conventional compact
group representation ring uses the independent theorem that finite-dimensional
complex representations are classified by characters.
-/

namespace GUT
namespace CharacterQuotient

open PhysicalRestrictionBridge

noncomputable section

universe u

def characterSetoid (G : Type u) [Group G] :
    Setoid (FiniteVirtualGroupRepresentation G) where
  r := FiniteVirtualGroupRepresentation.CharacterEquivalent
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h g => (h g).symm
    trans := fun h₁ h₂ g => (h₁ g).trans (h₂ g) }

/-- Finite virtual `G`-representations modulo equality of whole-group characters. -/
abbrev VirtualCharacterQuotient (G : Type u) [Group G] :=
  Quotient (characterSetoid G)

def mk {G : Type u} [Group G]
    (chi : FiniteVirtualGroupRepresentation G) : VirtualCharacterQuotient G :=
  Quotient.mk (characterSetoid G) chi

/-- The character function represented by a virtual-character quotient class. -/
def character {G : Type u} [Group G] :
    VirtualCharacterQuotient G -> G -> ℂ :=
  Quotient.lift FiniteVirtualGroupRepresentation.character (by
    intro chi psi h
    funext g
    exact h g)

@[simp]
theorem character_mk {G : Type u} [Group G]
    (chi : FiniteVirtualGroupRepresentation G) :
    character (mk chi) = FiniteVirtualGroupRepresentation.character chi :=
  rfl

abbrev SU6 := PhysicalRestrictionBridge.SU6
abbrev FiniteVirtualSU6Representation :=
  PhysicalRestrictionBridge.FiniteVirtualSU6Representation

def asGroupActual (R : ActualSU6Representation) :
    ActualGroupRepresentation SU6 where
  V := R.V
  instAddCommGroup := R.instAddCommGroup
  instModule := R.instModule
  instFiniteDimensional := R.instFiniteDimensional
  rho := R.rho

def asGroupVirtual :
    FiniteVirtualSU6Representation -> FiniteVirtualGroupRepresentation SU6
  | [] => []
  | s :: ss =>
      ⟨s.coeff, asGroupActual s.rep⟩ :: asGroupVirtual ss

def su6Character (chi : FiniteVirtualSU6Representation) : SU6 -> ℂ :=
  FiniteVirtualGroupRepresentation.character (asGroupVirtual chi)

def su6CharacterSetoid : Setoid FiniteVirtualSU6Representation where
  r chi psi := ∀ g, su6Character chi g = su6Character psi g
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h g => (h g).symm
    trans := fun h₁ h₂ g => (h₁ g).trans (h₂ g) }

/-- Finite virtual `SU(6)` representations modulo whole-group character equality. -/
abbrev SU6VirtualCharacterQuotient := Quotient su6CharacterSetoid

def su6Mk (chi : FiniteVirtualSU6Representation) :
    SU6VirtualCharacterQuotient :=
  Quotient.mk su6CharacterSetoid chi

def su6QuotientCharacter : SU6VirtualCharacterQuotient -> SU6 -> ℂ :=
  Quotient.lift su6Character (by
    intro chi psi h
    funext g
    exact h g)

@[simp]
theorem su6QuotientCharacter_mk (chi : FiniteVirtualSU6Representation) :
    su6QuotientCharacter (su6Mk chi) = su6Character chi :=
  rfl

/-- Restriction of finite virtual characters is evaluation after the group homomorphism. -/
theorem restrictVirtual_character
    {G : Type u} [Group G] (iota : G →* SU6)
    (chi : FiniteVirtualSU6Representation) (g : G) :
    FiniteVirtualGroupRepresentation.character (restrictVirtual iota chi) g =
      su6Character chi (iota g) := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      change
        (s.coeff : ℂ) *
            Representation.character
              (s.rep.rho.comp iota : Representation ℂ G s.rep.V) g +
            FiniteVirtualGroupRepresentation.character
              (restrictVirtual iota ss) g =
          (s.coeff : ℂ) * s.rep.rho.character (iota g) +
            su6Character ss (iota g)
      rw [ih]
      rfl

/-- Restriction descends to virtual-character quotient classes. -/
def restriction {G : Type u} [Group G] (iota : G →* SU6) :
    SU6VirtualCharacterQuotient -> VirtualCharacterQuotient G :=
  Quotient.map (restrictVirtual iota) (by
    intro chi psi h g
    rw [restrictVirtual_character, restrictVirtual_character]
    exact h (iota g))

theorem character_restriction
    {G : Type u} [Group G] (iota : G →* SU6)
    (chi : SU6VirtualCharacterQuotient) (g : G) :
    character (restriction iota chi) g = su6QuotientCharacter chi (iota g) := by
  refine Quotient.inductionOn chi ?_
  intro representative
  exact restrictVirtual_character iota representative g

/--
The concrete physical target remains outside the restriction image after both
source and target finite-virtual presentations are quotiented by character
equality.
-/
theorem flippedSMTarget_not_mem_quotientRestrictionImage :
    mk FlippedSMTarget.target ∉
      Set.range (restriction FlippedSMGroup.embedding) := by
  intro h
  rcases h with ⟨source, hsource⟩
  revert hsource
  refine Quotient.inductionOn source ?_
  intro chi hsource
  change mk (restrictVirtual FlippedSMGroup.embedding chi) =
    mk FlippedSMTarget.target at hsource
  apply FlippedSMTarget.no_flippedSMTarget_characterEquivalent_restriction
  refine ⟨chi, ?_⟩
  intro g
  have hcharacter := congrArg
    (fun q : VirtualCharacterQuotient FlippedSMGroup.Group => character q g)
    hsource
  simpa only [character_mk] using hcharacter

end

end CharacterQuotient
end GUT
