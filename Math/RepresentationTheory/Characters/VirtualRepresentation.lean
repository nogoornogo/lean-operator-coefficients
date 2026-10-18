import Mathlib.RepresentationTheory.Character
import Mathlib.Basic.Complex.Basic

/-! # Finite virtual representations of an arbitrary group -/

namespace Math.PhysicalRestrictionBridge
noncomputable section
universe u

/-- An actual finite-dimensional complex representation of a target group. -/
structure ActualGroupRepresentation (G : Type u) [Group G] where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  rho : Representation ℂ G V

attribute [instance] ActualGroupRepresentation.instAddCommGroup
attribute [instance] ActualGroupRepresentation.instModule
attribute [instance] ActualGroupRepresentation.instFiniteDimensional

namespace ActualGroupRepresentation

def character {G : Type u} [Group G]
    (R : ActualGroupRepresentation G) (g : G) : ℂ :=
  R.rho.character g

end ActualGroupRepresentation

/-- A finite virtual summand for the target group. -/
structure VirtualGroupSummand (G : Type u) [Group G] where
  coeff : ℤ
  rep : ActualGroupRepresentation G

namespace VirtualGroupSummand

def character {G : Type u} [Group G]
    (s : VirtualGroupSummand G) (g : G) : ℂ :=
  (s.coeff : ℂ) * s.rep.character g

end VirtualGroupSummand

abbrev FiniteVirtualGroupRepresentation (G : Type u) [Group G] :=
  List (VirtualGroupSummand G)

namespace FiniteVirtualGroupRepresentation

def character {G : Type u} [Group G] :
    FiniteVirtualGroupRepresentation G -> G -> ℂ
  | [], _ => 0
  | s :: ss, g => s.character g + character ss g

/-- Equality at the level of virtual characters on the whole target group. -/
def CharacterEquivalent {G : Type u} [Group G]
    (chi psi : FiniteVirtualGroupRepresentation G) : Prop :=
  ∀ g, character chi g = character psi g

end FiniteVirtualGroupRepresentation

end
end Math.PhysicalRestrictionBridge
