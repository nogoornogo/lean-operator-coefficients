import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Physics.FieldTheory.Mass.Spectrum.UnitaryVirtualRealization

/-! Transport of a symmetric mass along equality of bundled actual fields. -/

set_option autoImplicit false

namespace Physics.SymmetricMassTransport

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

/-- A constructed certificate keeps concrete equality transports out of radical types. -/
structure TransportCertificate (B : SymmetricMass S.rho) where
  mass : SymmetricMass R.rho
  mass_heq : HEq mass B
  nonzero_iff : mass.form ≠ 0 ↔ B.form ≠ 0
  radicalEquiv : Representation.Equiv mass.radical.toRepresentation B.radical.toRepresentation
  radical_finrank : Module.finrank ℂ mass.radical.toSubmodule =
    Module.finrank ℂ B.radical.toSubmodule
  radical_character : ∀ g : G, mass.radical.toRepresentation.character g =
    B.radical.toRepresentation.character g

/-- This certificate is proved for every equality, not supplied as an assumption. -/
def certificate (h : R = S) (B : SymmetricMass S.rho) : TransportCertificate (R := R) B :=
  Classical.choice ⟨{
    mass := transport h B
    mass_heq := transport_heq h B
    nonzero_iff := form_nonzero h B
    radicalEquiv := radicalEquiv h B
    radical_finrank := radical_finrank h B
    radical_character := radical_character h B }⟩

end

end Physics.SymmetricMassTransport
