import GUT.Spin10.SelectionRules.StandardChain
import GUT.Spin10.SU5Branching
import GUT.SU5.Branching.TorusMatterCharacter

open Physics

open Math

/-! An inhabited continuous standard-chain model on the actual compact
half-spin 16. Residual symmetry acts trivially and the mass is zero.
The positive one-generation target and one neutral singlet are derived
from actual traces, not supplied as branching or light-target certificates. -/

set_option autoImplicit false

namespace GUT.CompactSpin.HalfSpinBenchmark

open Math.CompactSpin
noncomputable section

open GUT.SU5 Physics.SU5 InvariantWeylMass FiniteAbelianChargeSectors
open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget

abbrev Space := HalfSpin.HilbertSpace 5

variable (H : Type*) [CommGroup H]

def rho : Representation ℂ (CompactSpin.Group 10 × H) Space :=
  (HalfSpin.unitaryModel 5).toRepresentation.comp (MonoidHom.fst _ _)

theorem unitary : UnitaryMultiplicity.IsUnitaryRepresentation (rho H) :=
  fun g => (HalfSpin.unitaryModel_unitary 5).inner_map_map g.1

@[simp] theorem residual_trivial (h : H) : rho H (1, h) = 1 := by
  change ((HalfSpin.unitaryModel 5).toRepresentation :
    Representation ℂ (CompactSpin.Group 10) Space) (1 : CompactSpin.Group 10) = 1
  exact map_one _

def family : FiniteChargeProfiles.Family (ChargeLabel H) :=
  ⟨FiniteChargeProfiles.pure 1 (sectorCharges 0 0), 1, by decide,
    FiniteChargeProfiles.pure_totals _ _⟩

def singlets : ChargeLabel H →₀ ℤ := Finsupp.single 0 1

theorem target_eval (g : TorusCharacter.CombinedGroup H) :
    TorusCharacter.eval
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) g =
      1 + TorusCharacter.eval (exactSMResolvedCharacter 1 (sectorCharges 0 0)) g := by
  change TorusCharacter.eval (FiniteChargeProfiles.targetWithSinglets
    (FiniteChargeProfiles.pure 1 (sectorCharges 0 0)) (singlets H)) g = _
  rw [FiniteChargeProfiles.targetWithSinglets_pure, exactSMWithSingletsResolvedCharacter,
    ← TorusCharacter.evalAddHom_apply, map_add]
  simp only [TorusCharacter.evalAddHom_apply, singlets, singletResolvedCharacter,
    Finsupp.mapDomain_single, TorusCharacter.eval_single, Int.cast_one, one_mul]
  have hk : TorusCharacter.keyCharacter (0, (0 : ChargeLabel H)) g = 1 := by
    change (TorusCharacter.weightCharacter 0 g.1 : ℂ) * 1 = 1
    have hz : rawReducedWeight 0 = 0 := by ext i; fin_cases i <;> rfl
    simp [TorusCharacter.weightCharacter, TorusCharacter.rawCharacter, hz]
  rw [hk, add_comm]
  simp only [Nat.cast_one]

theorem restricted_character (g : TorusCharacter.CombinedGroup H) :
    (rho H).character (SU5Inclusion (MaximalTorus.hom g.1), g.2) =
      TorusCharacter.eval
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) g := by
  change (HalfSpin.unitaryModel 5).toRepresentation.character
    (SU5Inclusion (MaximalTorus.hom g.1)) = _
  rw [SU5Branching.unitary_character, target_eval, add_assoc]
  have hp := TorusMatterCharacter.charged_pair_character (0 : ChargeLabel H) 0 g.1 g.2
  have hz (h : H) : ((0 : ChargeLabel H).toMul h : ℂ) = 1 := rfl
  simpa only [hz, mul_one] using congrArg (fun z : ℂ => 1 + z) hp

theorem restricted_dual_index (g : TorusCharacter.CombinedGroup H) :
    (TorusCharacterSource.restrict (GUT.StandardChain.pullback SU5Inclusion (rho H))).character g -
      (TorusCharacterSource.restrict (GUT.StandardChain.pullback SU5Inclusion (rho H))).dual.character g =
      TorusCharacter.eval (chiralDifference
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H))) g := by
  rw [Representation.char_dual]
  change (rho H).character (SU5Inclusion (MaximalTorus.hom g.1), g.2) -
    (rho H).character (SU5Inclusion (MaximalTorus.hom g.1⁻¹), g.2⁻¹) = _
  rw [restricted_character H g, restricted_character H (g.1⁻¹, g.2⁻¹),
    TorusCharacter.eval_chiralDifference]
  rfl

/-- Invariant masses preserve the dual index; zero mass is only the concrete
choice made below, not a premise of this target theorem. -/
theorem hasTarget (B : SymmetricMass (TorusCharacterSource.restrict
    (GUT.StandardChain.pullback SU5Inclusion (rho H)))) :
    TorusMassSource.HasTarget (GUT.StandardChain.pullback SU5Inclusion (rho H))
      B (family H).profiles (singlets H) :=
  fun g => (B.radical_dual_character_eq g).trans (restricted_dual_index H g)

def model : StandardChain.Model (rho H) where
  unitary := unitary H
  mass := SymmetricMass.zero _
  profile := family H
  singlets := singlets H
  lightTarget := hasTarget H _

theorem rho_continuous [TopologicalSpace H] :
    Continuous (fun p : (CompactSpin.Group 10 × H) × Space => rho H p.1 p.2) := by
  change Continuous (fun p : (CompactSpin.Group 10 × H) × Space =>
    HalfSpin.unitaryModel 5 p.1.1 p.2)
  have hc : Continuous (fun p : (CompactSpin.Group 10 × H) × Space => (p.1.1, p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  exact Continuous.comp (f := fun p : (CompactSpin.Group 10 × H) × Space => (p.1.1, p.2))
    (g := fun p : CompactSpin.Group 10 × Space => HalfSpin.unitaryModel 5 p.1 p.2)
    (HalfSpin.unitaryModel_continuous 5) hc

def continuousModel [TopologicalSpace H] [IsTopologicalGroup H] :
    GUT.StandardChain.ContinuousModel SU5Inclusion (rho H) :=
  StandardChain.continuousModel (model H) (rho_continuous H)

theorem radical_top : (model H).mass.radical.toSubmodule = ⊤ :=
  SymmetricMass.radical_zero

theorem radical_finrank : Module.finrank ℂ (model H).mass.radical.toSubmodule = 16 := by
  rw [radical_top, finrank_top, HalfSpin.hilbert_finrank_sixteen]

def radicalEquiv : Representation.Equiv (model H).mass.radical.toRepresentation
    ((rho H).comp (GUT.StandardChain.torusInclusion SU5Inclusion)) :=
  (CharacterExact.subtypeIntertwiner (model H).mass.radical).ofBijective
    ⟨Subtype.val_injective, fun v => ⟨⟨v, by rw [radical_top]; trivial⟩, rfl⟩⟩

theorem radical_character (g : TorusCharacter.CombinedGroup H) :
    (model H).mass.radical.toRepresentation.character g =
      TorusCharacter.eval
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) g :=
  (congrFun (Representation.char_iso (radicalEquiv H)) g).trans (restricted_character H g)

/-- The zero-mass example has the full target spectrum, not merely its dual index. -/
theorem lightSpectrum_eq : (model H).lightSpectrum =
    FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H) :=
  TorusMassSource.spectrum_eq_of_character
    (GUT.StandardChain.pullback SU5Inclusion (rho H))
    (GUT.StandardChain.pullback_unitary SU5Inclusion (rho H) (model H).unitary)
    (model H).mass _ (radical_character H)

theorem profile_at_smWeight (i : Fin 15) :
    StandardSMCharacterTarget.smCharge (family H).profiles i (0 : ChargeLabel H) = 1 := by
  fin_cases i <;> simp [family, FiniteChargeProfiles.pure,
    StandardSMCharacterTarget.smCharge, sectorCharges]

theorem light_index_coefficient (i : Fin 15) :
    chiralDifference (model H).lightSpectrum (smReducedWeight i, (0 : ChargeLabel H)) = 1 := by
  rw [lightSpectrum_eq, FiniteChargeProfiles.chiralDifference_target_apply,
    profile_at_smWeight, Nat.cast_one]

theorem light_singlet_coefficient : (model H).lightSpectrum (0, (0 : ChargeLabel H)) = 1 := by
  classical
  rw [lightSpectrum_eq]
  simp [family, FiniteChargeProfiles.targetWithSinglets_pure,
    exactSMWithSingletsResolvedCharacter, exactSMResolvedCharacter, smResolvedKey,
    singletResolvedCharacter, singlets, smReducedWeight_nonzero]

theorem exists_sm_zeroMode (i : Fin 15) :
    ∃ v : (model H).mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, (model H).mass.radical.toRepresentation g v =
        TorusCharacter.keyCharacter (smReducedWeight i, (0 : ChargeLabel H)) g • v := by
  apply TorusMassSource.exists_zeroMode _
    (GUT.StandardChain.pullback_unitary SU5Inclusion _ (model H).unitary)
    (model H).mass _ _ (model H).lightTarget i 0
  change 0 < StandardSMCharacterTarget.smCharge (family H).profiles i (0 : ChargeLabel H)
  rw [profile_at_smWeight]
  decide

theorem nonvacuous :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (model H).lightSpectrum := (model H).selection_rule_obstruction

end

end GUT.CompactSpin.HalfSpinBenchmark
