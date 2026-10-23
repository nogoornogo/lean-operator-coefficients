import GUT.SU5.Branching.TorusCharacterSource
import GUT.SU5.Embeddings.PhysicalTorus
import Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum
import Physics.StandardModel.Spectrum.Charges.ProfileChiralIndex
import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator

open Physics

open Math Physics

/-!
# Arbitrary SU(5) matter with an exact dual light target

The source is an actual unitary representation of SU(5) times an arbitrary
Abelian residual group. Its symmetric mass need only be invariant on the
diagonal torus times that group. The target is an explicit infrared input;
Weyl/profile compatibility and actual radical support are derived.

Determinant-one torus coordinates are related to the actual SM embedding by
PhysicalTorus, with no extra assumed invariance certificate. The conclusion concerns supported neutral
signatures, not a nonzero amplitude or a general full-gauge radical tensor.
-/

set_option autoImplicit false

namespace GUT.SU5.TorusMassSource
open Physics.SU5

noncomputable section

open StandardModelEmbedding TorusCharacter TorusCharacterSource
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StandardBranchProtonObstruction StandardModelLocalOperator

variable {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ (TargetGroup × H) E)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
  (B : SymmetricMass (restrict rho))

omit [FiniteDimensional ℂ E] in
include hu in
theorem restricted_unitary : UnitaryMultiplicity.IsUnitaryRepresentation (restrict rho) :=
  fun g v w => hu (inclusion g) v w

def HasTarget (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ) : Prop :=
  ∀ g, B.radical.toRepresentation.character g - B.radical.toRepresentation.dual.character g =
    TorusCharacter.eval (chiralDifference (targetWithSinglets P s)) g

omit [FiniteDimensional ℂ E] in
/-- Physical covering coordinates suffice: their SU(5) torus map is
surjective, including its finite kernel. -/
theorem hasTarget_iff_physical (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ) :
    HasTarget rho B P s ↔ ∀ z h,
      B.radical.toRepresentation.character (PhysicalTorus.toTorus z, h) -
          B.radical.toRepresentation.dual.character (PhysicalTorus.toTorus z, h) =
        TorusCharacter.eval (chiralDifference (targetWithSinglets P s))
          (PhysicalTorus.toTorus z, h) := by
  constructor
  · intro ht z h
    exact ht _
  · intro ht g
    obtain ⟨z, hz⟩ := PhysicalTorus.toTorus_surjective g.1
    simpa only [hz] using ht z g.2

variable (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)

theorem source_target (ht : HasTarget rho B P s) (g : TorusCharacter.CombinedGroup H) :
    (restrict rho).character g - (restrict rho).dual.character g =
      TorusCharacter.eval (chiralDifference (targetWithSinglets P s)) g :=
  (B.radical_dual_character_eq g).symm.trans (ht g)

theorem profiles_compatible (ht : HasTarget rho B P s) : OrbitCompatible P :=
  orbitCompatible_of_dual_invariant P s
    (target_invariant rho _ (source_target rho B P s ht))

/-- The actual radical multiplicities at integral SU(5) torus weights.
This is a pullback of the full character spectrum, not an assertion that
every character of an abstract source is an integral torus character. -/
def spectrum : ResolvedCharacter (ChargeLabel H) :=
  Finsupp.comapDomain keyCharacter
    (Physics.AbelianMassSpectrum.radicalSpectrum B (restricted_unitary rho hu)) keyCharacter_injective.injOn

theorem spectrum_nonneg (key : ResolvedKey (ChargeLabel H)) : 0 ≤ spectrum rho hu B key :=
  Physics.AbelianMassSpectrum.radicalSpectrum_nonneg B (restricted_unitary rho hu) _

/-- A full radical trace identity determines its resolved spectrum, unlike
the weaker dual-index target. -/
theorem spectrum_eq_of_character (p : ResolvedCharacter (ChargeLabel H))
    (hc : ∀ g, B.radical.toRepresentation.character g = TorusCharacter.eval p g) :
    spectrum rho hu B = p := by
  have he : Physics.AbelianMassSpectrum.radicalSpectrum B (restricted_unitary rho hu) = lift p := by
    apply AbelianActualSpectrum.eval_injective
    intro g
    rw [Physics.AbelianMassSpectrum.radicalSpectrum_eval, eval_lift, hc]
  ext key
  have hh := congrArg (fun q : AbelianActualSpectrum.Polynomial (TorusCharacter.CombinedGroup H) =>
    q (keyCharacter key)) he
  simpa only [spectrum, Finsupp.comapDomain_apply, lift,
    Finsupp.mapDomain_apply_of_injective keyCharacter_injective] using hh

theorem chiral_spectrum (ht : HasTarget rho B P s) :
    chiralDifference (spectrum rho hu B) = chiralDifference (targetWithSinglets P s) := by
  have he := Physics.AbelianMassSpectrum.radical_dual_spectrum_eq_target B (restricted_unitary rho hu)
    (lift (chiralDifference (targetWithSinglets P s))) (by
      intro g
      rw [eval_lift]
      exact source_target rho B P s ht g)
  ext key
  have hh := congrArg (fun p : AbelianActualSpectrum.Polynomial (TorusCharacter.CombinedGroup H) =>
    p (keyCharacter key)) he
  simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    spectrum, Finsupp.comapDomain_apply, AbelianActualSpectrum.dual_apply, keyCharacter_neg,
    lift, Finsupp.mapDomain_apply_of_injective keyCharacter_injective] using hh

include hu in
theorem exists_zeroMode (ht : HasTarget rho B P s) (i : Fin 15) (q : ChargeLabel H)
    (hq : 0 < smCharge P i q) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyCharacter (smReducedWeight i, q) g • v := by
  apply UnitaryCharacterSpectrum.exists_eigenvector_of_coeff_ne_zero
    B.radical.toRepresentation (Physics.AbelianMassSpectrum.radical_unitary B (restricted_unitary rho hu))
  have hp := coefficient_lower_bound P s _ (spectrum_nonneg rho hu B)
    (chiral_spectrum rho hu B P s ht) i q
  change spectrum rho hu B (smReducedWeight i, q) ≠ 0
  omega

theorem chargesSupported (ht : HasTarget rho B P s)
    (k : Charges (ChargeLabel H)) (hk : Occupied P k) :
    ChargesSupported (spectrum rho hu B) k :=
  chargesSupported_of_occupied P s _ (spectrum_nonneg rho hu B)
    (chiral_spectrum rho hu B P s ht) k hk

variable (F : Family (ChargeLabel H))

/-- Both signatures use actual occupied radical modes and source-derived
charge equalities. No support or Weyl-invariance field is supplied. -/
theorem exists_actual_signature_pair (ht : HasTarget rho B F.profiles s) :
    ∃ Q D : SupportedInvariantOperator (spectrum rho hu B),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey Q.charges i) g • v := by
  obtain ⟨k, hk, hQ, hD⟩ := exists_occupied_trivial_characters F
    (profiles_compatible rho B F.profiles s ht)
  have hs := chargesSupported rho hu B F.profiles s ht k hk
  refine ⟨supportedQque k hs hQ, supportedDuql k hs hD, rfl, rfl, rfl, ?_⟩
  intro i
  exact exists_zeroMode rho hu B F.profiles s ht i _
    (smCharge_pos_of_occupied F.profiles k hk i)

theorem selection_rule_obstruction (ht : HasTarget rho B F.profiles s) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (spectrum rho hu B) := by
  obtain ⟨Q, _, _⟩ := exists_actual_signature_pair rho hu B s F ht
  exact Q.not_forbidsEverySupportedPhysicalDeltaBOneOperator

end

end GUT.SU5.TorusMassSource
