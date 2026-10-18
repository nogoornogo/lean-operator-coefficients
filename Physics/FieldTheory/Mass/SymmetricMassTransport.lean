import Physics.FieldTheory.Mass.InvariantWeylMass
import Physics.FieldTheory.Mass.UnitaryVirtualRealization

/-! Transport of a symmetric mass along equality of bundled actual fields. -/

set_option autoImplicit false

namespace GUT.SymmetricMassTransport

noncomputable section

open UnitaryVirtualRealization InvariantWeylMass

variable {G : Type*} [Group G] {R S : ActualUnitaryGroupRepresentation G}

def transport (h : R = S) (B : SymmetricMass S.rho) : SymmetricMass R.rho := h ▸ B

theorem transport_heq (h : R = S) (B : SymmetricMass S.rho) : HEq (transport h B) B := by
  subst S
  rfl

theorem form_nonzero (h : R = S) (B : SymmetricMass S.rho) :
    (transport h B).form ≠ 0 ↔ B.form ≠ 0 := by
  subst S
  rfl

def radicalEquiv (h : R = S) (B : SymmetricMass S.rho) :
    Representation.Equiv (transport h B).radical.toRepresentation B.radical.toRepresentation := by
  subst S
  exact Representation.Equiv.refl _

theorem radical_finrank (h : R = S) (B : SymmetricMass S.rho) :
    Module.finrank ℂ (transport h B).radical.toSubmodule =
      Module.finrank ℂ B.radical.toSubmodule := by
  subst S
  rfl

theorem radical_character (h : R = S) (B : SymmetricMass S.rho) (g : G) :
    (transport h B).radical.toRepresentation.character g =
      B.radical.toRepresentation.character g := by
  subst S
  rfl

end

end GUT.SymmetricMassTransport
