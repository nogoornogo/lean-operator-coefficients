import Physics.StandardModel.Spectrum.RestrictedConjugationMassSource

open Math

/-! Compatibility API for ambient-unitary, common-total models. The shared
core requires only restricted unitarity and independent positive orbit totals. -/

set_option autoImplicit false

namespace GUT.StructuralConjugationMass

noncomputable section

open SU5 SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StandardBranchProtonObstruction StandardModelLocalOperator

variable {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
  (B : SymmetricMass (restrict j rho))

omit [FiniteDimensional ℂ E] in
include hu in
theorem restricted_unitary : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho) :=
  fun g v w => hu (inclusion j g) v w

variable (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)

/-- Actual radical coefficients at the chosen integral weight characters.
No completeness claim about the full spectrum follows from a dual target. -/
def spectrum : ResolvedCharacter (ChargeLabel H) :=
  RestrictedUnitary.spectrum j rho B (restricted_unitary j rho hu)

theorem spectrum_eq_restricted : spectrum j rho hu B =
    RestrictedUnitary.spectrum j rho B (restricted_unitary j rho hu) := rfl

theorem spectrum_nonneg (key : ResolvedKey (ChargeLabel H)) :
    0 ≤ spectrum j rho hu B key :=
  RestrictedUnitary.spectrum_nonneg j rho B (restricted_unitary j rho hu) key

theorem chiral_spectrum (ht : HasTarget j rho B P s) :
    chiralDifference (spectrum j rho hu B) = chiralDifference (targetWithSinglets P s) :=
  RestrictedUnitary.chiral_spectrum j rho B P s (restricted_unitary j rho hu) ht

include hu in
theorem exists_zeroMode (ht : HasTarget j rho B P s) (i : Fin 15) (q : ChargeLabel H)
    (hq : 0 < smCharge P i q) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyCharacter (smReducedWeight i, q) g • v :=
  RestrictedUnitary.exists_zeroMode j rho B P s (restricted_unitary j rho hu) ht i q hq

theorem chargesSupported (ht : HasTarget j rho B P s)
    (k : Charges (ChargeLabel H)) (hk : Occupied P k) :
    ChargesSupported (spectrum j rho hu B) k :=
  RestrictedUnitary.chargesSupported j rho B P s (restricted_unitary j rho hu) ht k hk

variable (F : Family (ChargeLabel H))

theorem exists_actual_signature_pair (c : ThreeConjugations j)
    (ht : HasTarget j rho B F.profiles s) :
    ∃ Q D : SupportedInvariantOperator (spectrum j rho hu B),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey Q.charges i) g • v :=
  RestrictedUnitary.exists_actual_signature_pair j rho B F.profiles s
    (restricted_unitary j rho hu) (F.totals.quark ▸ F.positive)
    (F.totals.down ▸ F.positive) c ht

theorem selection_rule_obstruction (c : ThreeConjugations j)
    (ht : HasTarget j rho B F.profiles s) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (spectrum j rho hu B) := by
  obtain ⟨Q, _, _⟩ := exists_actual_signature_pair j rho hu B s F c ht
  exact Q.not_forbidsEverySupportedPhysicalDeltaBOneOperator

end
end GUT.StructuralConjugationMass
