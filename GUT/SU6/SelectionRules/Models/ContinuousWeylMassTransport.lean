import GUT.SU6.SelectionRules.StandardBranch.StandardWeylFieldIdentification
import Physics.FieldTheory.Mass.SymmetricMassTransport

open Math

/-!
# A mass-preserving continuous-geometry adapter

Unlike `ofStandardWithZeroMass`, this adapter transports the given mass along
equality of the canonical actual fields. The radical representation and the
full light spectrum are preserved, not only their dual indices.
-/

set_option autoImplicit false

namespace GUT.ContinuousWeylMassTransport

noncomputable section

open StandardWeylMassSource ContinuousWeylModel PhysicalWeylMassSource

variable {H : Type*} [CommGroup H]

def ofStandard (M : StandardWeylModel H) : ContinuousWeylMassModel H where
  geometry := ConcreteStandardGeometry.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  mass := SymmetricMassTransport.transport
    (StandardWeylFieldIdentification.continuous_fields_eq M.matter) M.mass
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := by
    apply lightTarget_of_dualResolved _ _ _ M.nonnegative
    rw [ConcreteStandardGeometry.hyperchargePair_eq_standard]
    exact ContinuousWeylBenchmark.standardSource_dualTarget M

theorem mass_heq (M : StandardWeylModel H) : HEq (ofStandard M).mass M.mass :=
  SymmetricMassTransport.transport_heq (StandardWeylFieldIdentification.continuous_fields_eq M.matter) M.mass

theorem mass_nonzero_iff (M : StandardWeylModel H) :
    (ofStandard M).mass.form ≠ 0 ↔ M.mass.form ≠ 0 :=
  SymmetricMassTransport.form_nonzero (StandardWeylFieldIdentification.continuous_fields_eq M.matter) M.mass

def radicalEquiv (M : StandardWeylModel H) :
    Representation.Equiv (ofStandard M).mass.radical.toRepresentation M.mass.radical.toRepresentation :=
  SymmetricMassTransport.radicalEquiv (StandardWeylFieldIdentification.continuous_fields_eq M.matter) M.mass

theorem radical_finrank (M : StandardWeylModel H) :
    Module.finrank ℂ (ofStandard M).mass.radical.toSubmodule =
      Module.finrank ℂ M.mass.radical.toSubmodule :=
  SymmetricMassTransport.radical_finrank (StandardWeylFieldIdentification.continuous_fields_eq M.matter) M.mass

theorem radical_character (M : StandardWeylModel H) (g : StandardSMCharacterTarget.CombinedGroup H) :
    (ofStandard M).mass.radical.toRepresentation.character g = M.mass.radical.toRepresentation.character g :=
  SymmetricMassTransport.radical_character (StandardWeylFieldIdentification.continuous_fields_eq M.matter) M.mass g

theorem actualSpectrum (M : StandardWeylModel H) :
    AbelianActualSpectrum.spectrum (PhysicalWeylZeroModeSupport.lightRepresentation (ofStandard M).toPhysical) =
      AbelianActualSpectrum.spectrum (WeylZeroModeSupport.lightRepresentation M) := by
  apply AbelianActualSpectrum.eval_injective
  intro g
  rw [AbelianActualSpectrum.spectrum_eval, AbelianActualSpectrum.spectrum_eval]
  exact radical_character M g

theorem lightSpectrum (M : StandardWeylModel H) :
    PhysicalWeylZeroModeSupport.lightSpectrum (ofStandard M).toPhysical =
      WeylZeroModeSupport.lightSpectrum M := by
  ext key
  rw [PhysicalWeylZeroModeSupport.lightSpectrum_apply, WeylZeroModeSupport.lightSpectrum_apply,
    actualSpectrum]

end

end GUT.ContinuousWeylMassTransport
