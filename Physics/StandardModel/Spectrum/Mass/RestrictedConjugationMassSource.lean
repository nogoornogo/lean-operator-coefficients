import Physics.StandardModel.Spectrum.Representations.ConjugationSource
import Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum
import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator

open Math Physics

/-! Actual mass endpoint with only restricted unitarity and independent
positive orbit totals. Ambient conjugations need not preserve the mass. -/

set_option autoImplicit false

namespace Physics.StructuralConjugationMass

noncomputable section

open SU5 SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StandardBranchProtonObstruction StandardModelLocalOperator

variable {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))

def HasTarget (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ) : Prop :=
  ∀ g, B.radical.toRepresentation.character g - B.radical.toRepresentation.dual.character g =
    TorusCharacter.eval (chiralDifference (targetWithSinglets P s)) g

variable (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)

/-- Only the dual index is transported. No radical conjugation is asserted. -/
theorem source_target (ht : HasTarget j rho B P s) (g : CombinedGroup H) :
    (restrict j rho).character g - (restrict j rho).dual.character g =
      TorusCharacter.eval (chiralDifference (targetWithSinglets P s)) g :=
  (B.radical_dual_character_eq g).symm.trans (ht g)

theorem profiles_compatible (c : ThreeConjugations j) (ht : HasTarget j rho B P s) :
    OrbitCompatible P :=
  StructuralConjugation.profiles_compatible c rho P s (source_target j rho B P s ht)

namespace RestrictedUnitary

variable (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))

/-- Actual radical coefficients at integral weight characters. A dual target
does not determine the full spectrum. -/
def spectrum : ResolvedCharacter (ChargeLabel H) :=
  Finsupp.comapDomain keyCharacter (Physics.AbelianMassSpectrum.radicalSpectrum B hu)
    keyCharacter_injective.injOn

theorem spectrum_nonneg (key : ResolvedKey (ChargeLabel H)) :
    0 ≤ spectrum j rho B hu key :=
  Physics.AbelianMassSpectrum.radicalSpectrum_nonneg B hu _

theorem chiral_spectrum (ht : HasTarget j rho B P s) :
    chiralDifference (spectrum j rho B hu) = chiralDifference (targetWithSinglets P s) := by
  have he := Physics.AbelianMassSpectrum.radical_dual_spectrum_eq_target B hu
    (lift (chiralDifference (targetWithSinglets P s))) (by
      intro g
      rw [eval_lift]
      exact source_target j rho B P s ht g)
  ext key
  have hh := congrArg (fun p : AbelianActualSpectrum.Polynomial (CombinedGroup H) =>
    p (keyCharacter key)) he
  simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    spectrum, Finsupp.comapDomain_apply, AbelianActualSpectrum.dual_apply, keyCharacter_neg,
    lift, Finsupp.mapDomain_apply_of_injective keyCharacter_injective] using hh

include hu in
theorem exists_zeroMode (ht : HasTarget j rho B P s) (i : Fin 15) (q : ChargeLabel H)
    (hq : 0 < smCharge P i q) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyCharacter (smReducedWeight i, q) g • v := by
  apply UnitaryCharacterSpectrum.exists_eigenvector_of_coeff_ne_zero
    B.radical.toRepresentation (Physics.AbelianMassSpectrum.radical_unitary B hu)
  have hp := coefficient_lower_bound P s _ (spectrum_nonneg j rho B hu)
    (chiral_spectrum j rho B P s hu ht) i q
  change spectrum j rho B hu (smReducedWeight i, q) ≠ 0
  omega

theorem chargesSupported (ht : HasTarget j rho B P s)
    (k : Charges (ChargeLabel H)) (hk : Occupied P k) :
    ChargesSupported (spectrum j rho B hu) k :=
  chargesSupported_of_occupied P s _ (spectrum_nonneg j rho B hu)
    (chiral_spectrum j rho B P s hu ht) k hk

theorem exists_actual_signature_pair (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (c : ThreeConjugations j) (ht : HasTarget j rho B P s) :
    ∃ Q D : SupportedInvariantOperator (spectrum j rho B hu),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey Q.charges i) g • v := by
  obtain ⟨k, hk, hq, hd⟩ := exists_occupied_trivial_characters_of_positive_totals P hQ hD
    (profiles_compatible j rho B P s c ht)
  have hs := chargesSupported j rho B P s hu ht k hk
  refine ⟨supportedQque k hs hq, supportedDuql k hs hd, rfl, rfl, rfl, ?_⟩
  intro i
  exact exists_zeroMode j rho B P s hu ht i _ (smCharge_pos_of_occupied P k hk i)

theorem selection_rule_obstruction (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (c : ThreeConjugations j) (ht : HasTarget j rho B P s) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (spectrum j rho B hu) := by
  obtain ⟨Q, _, _⟩ := exists_actual_signature_pair j rho B P s hu hQ hD c ht
  exact Q.not_forbidsEverySupportedPhysicalDeltaBOneOperator

end RestrictedUnitary
end
end Physics.StructuralConjugationMass
