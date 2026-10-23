import GUT.SU6.SelectionRules.Models.PhysicalWeylMassSource
import GUT.SU6.SelectionRules.Models.ProfileZeroModeSupport

open Physics

/-!
# Physical SU(6) sources for family-dependent SM profiles

The same dual light target fixes hypercharge after forgetting residual
charges and then forces equal profiles along the SU(5) Weyl orbits. These
equalities are derived from actual matter, not new applicability conditions.
-/

set_option autoImplicit false

namespace GUT.PhysicalProfileSource

noncomputable section

open StandardAbelianCharge StandardBranchProtonObstruction
open FiniteChargeProfiles (Family Profiles targetWithSinglets forgetCharges)
open PhysicalChargeResolvedBridge
  (PhysicalResolvedCharacter embedStandardCharacter forgetCharge ordinaryChargedSource
    ordinaryPhysicalResolvedCharacter sourcePhysicalResolvedCharacter)
open StandardPhysicalSource (FiniteChargedContinuousUnitarySource)
open StandardSMCharacterTarget (CombinedGroup ChargeLabel)
open InvariantWeylMass PhysicalMassSpectrumBridge
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)

variable {A : Type*} [AddCommGroup A]

omit [AddCommGroup A] in
theorem forget_embed (p : ResolvedCharacter A) :
    forgetCharge (embedStandardCharacter p) =
      Finsupp.mapDomain StandardSMCharacterTarget.standardExponent (forgetCharges p) := by
  simp only [forgetCharge, embedStandardCharacter, forgetCharges,
    ← Finsupp.mapDomain_comp]
  rfl

theorem forget_profile (F : Family A) (s : A →₀ ℤ) :
    forgetCharge (embedStandardCharacter (targetWithSinglets F.profiles s)) =
      PhysicalTorusCharacterBridge.exactSMCharacter (F.generations : ℤ)
        (PhysicalChargeResolvedBridge.totalSingletMultiplicity s) := by
  let k : Charges A := ⟨0, 0, 0, 0, 0⟩
  have he : forgetCharges (targetWithSinglets F.profiles s) =
      forgetCharges (targetWithSinglets (FiniteChargeProfiles.pure F.generations k) s) := by
    rw [FiniteChargeProfiles.forgetCharges_targetWithSinglets F.totals,
      FiniteChargeProfiles.forgetCharges_targetWithSinglets (FiniteChargeProfiles.pure_totals _ _)]
  rw [forget_embed, he, ← forget_embed, FiniteChargeProfiles.targetWithSinglets_pure,
    ← PhysicalChargeResolvedBridge.exactSMWithSingletsResolvedCharacter_standard,
    PhysicalChargeResolvedBridge.forgetCharge_exactSMWithSingletsResolvedCharacter]

theorem hypercharge_of_dual_profile (source : FiniteChargedContinuousUnitarySource A)
    (F : Family A) (s : A →₀ ℤ) (m n : ℤ)
    (ht : PhysicalWeylMomentBridge.chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      PhysicalWeylMomentBridge.chiralDifference (embedStandardCharacter (targetWithSinglets F.profiles s))) :
    m = -2 ∧ n = 3 := by
  have hi := congrArg forgetCharge ht
  simp only [PhysicalWeylChargeBridge.forgetCharge_chiralDifference,
    PhysicalChargeResolvedBridge.forgetCharge_sourcePhysicalResolvedCharacter, forget_profile] at hi
  have hr := congrArg PhysicalTorusCharacterBridge.toRationalCharacter hi
  have hn : (F.generations : ℤ) ≠ 0 := by exact_mod_cast F.generations_ne_zero
  have he := PhysicalWeylMomentBridge.eq_standard_of_virtualModel_dualRestriction
    source.ambientLaurentModel (F.generations : ℤ)
    (PhysicalChargeResolvedBridge.totalSingletMultiplicity s) (m : ℚ) (n : ℚ) hn
    (by simpa only [PhysicalWeylMomentBridge.IsDualSMRestriction,
      PhysicalWeylMomentBridge.toRationalCharacter_chiralDifference,
      PhysicalTorusCharacterBridge.toRationalCharacter_restrictIntegralCharacter,
      PhysicalTorusCharacterBridge.toRationalCharacter_exactSMCharacter] using hr)
  exact ⟨by exact_mod_cast he.1, by exact_mod_cast he.2⟩

theorem orbitCompatible_of_dual_profile (source : FiniteChargedContinuousUnitarySource A)
    (F : Family A) (s : A →₀ ℤ) (m n : ℤ)
    (ht : PhysicalWeylMomentBridge.chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      PhysicalWeylMomentBridge.chiralDifference (embedStandardCharacter (targetWithSinglets F.profiles s))) :
    FiniteChargeProfiles.OrbitCompatible F.profiles := by
  obtain ⟨rfl, rfl⟩ := hypercharge_of_dual_profile source F s m n ht
  apply FiniteChargeProfiles.orbitCompatible_of_dual_target F.profiles s
    (source.resolvedCharacter (0 : ℤ →+ A)) (source.resolvedCharacter_isWeylInvariant _)
  apply PhysicalChargeResolvedBridge.embedStandardCharacter_injective
  simpa only [PhysicalWeylChargeBridge.embedStandardCharacter_chiralDifference,
    PhysicalChargeResolvedBridge.sourcePhysicalResolvedCharacter_standard] using ht

variable {H : Type*} [CommGroup H]

/-- Conservation of the actual mass radical's dual character supplies the
source equality; no UV character certificate is an input. -/
theorem dualResolved_of_lightTarget (m n : ℤ) (matter : OrdinaryAbelianSource H)
    (hc : ∀ a ∈ matter, 0 ≤ a.coeff)
    (B : SymmetricMass (ordinaryPositiveRepresentation m n matter).rho)
    (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (ordinaryPositiveRepresentation m n matter) B P s) :
    PhysicalWeylMomentBridge.chiralDifference (ordinaryPhysicalResolvedCharacter m n matter) =
      PhysicalWeylMomentBridge.chiralDifference (embedStandardCharacter (targetWithSinglets P s)) := by
  apply PhysicalChargeResolvedEvaluation.eval_faithful
  intro x h
  rw [PhysicalWeylMassSource.eval_chiralDifference,
    ← PhysicalWeylMassSource.fields_character m n matter hc,
    ← PhysicalWeylMassSource.fields_character m n matter hc,
    ← PhysicalWeylChargeBridge.embedStandardCharacter_chiralDifference,
    PhysicalWeylMassSource.eval_embedStandardCharacter]
  have hu := ultravioletDualIndex_characterEquivalent_of_lightDualIndex B
    (ordinaryPositiveRepresentation m n matter).unitary _ ht (Multiplicative.ofAdd x, h)
  simpa only [dualIndex_character, Representation.char_dual,
    StandardSMCharacterTarget.character_ofCharacter, Prod.inv_mk, ofAdd_neg] using hu

theorem source_conclusions (m n : ℤ) (matter : OrdinaryAbelianSource H)
    (hc : ∀ a ∈ matter, 0 ≤ a.coeff)
    (B : SymmetricMass (ordinaryPositiveRepresentation m n matter).rho)
    (F : Family (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (ordinaryPositiveRepresentation m n matter) B F.profiles s) :
    (m = -2 ∧ n = 3) ∧ FiniteChargeProfiles.OrbitCompatible F.profiles := by
  have hd := dualResolved_of_lightTarget m n matter hc B F.profiles s ht
  exact ⟨hypercharge_of_dual_profile (ordinaryChargedSource matter) F s m n hd,
    orbitCompatible_of_dual_profile (ordinaryChargedSource matter) F s m n hd⟩

end

end GUT.PhysicalProfileSource
