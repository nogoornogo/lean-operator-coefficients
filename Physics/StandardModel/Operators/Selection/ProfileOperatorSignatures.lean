import Physics.StandardModel.Spectrum.Charges.FiniteChargeProfiles
import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator

open Math

/-!
# Neutral operator signatures in a finite profile target

This constructs the existing formal operator signatures supported by the
target coefficients. It does not construct actual mass-radical vectors,
full gauge intertwiners on a radical, or nonzero interaction coefficients.
-/

namespace Physics.FiniteChargeProfiles

noncomputable section

open StandardAbelianCharge StandardModelLocalOperator FiniteAbelianChargeSectors

/-- Both signatures are supported at the same occupied choice of charges. -/
theorem exists_supported_signature_pair {H : Type*} [CommGroup H]
    (F : Family (ChargeLabel H)) (h : OrbitCompatible F.profiles)
    (s : ChargeLabel H →₀ ℤ) :
    ∃ Q D : SupportedInvariantOperator (targetWithSinglets F.profiles s),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges := by
  obtain ⟨k, hk, hQ, hD⟩ := exists_occupied_trivial_characters F h
  have hs := (occupied_iff_supported_withSinglets F.profiles s k).mp hk
  exact ⟨supportedQque k hs hQ, supportedDuql k hs hD, rfl, rfl, rfl⟩

end

end Physics.FiniteChargeProfiles
