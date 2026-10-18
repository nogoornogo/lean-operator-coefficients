import GUT.E6.Minuscule.SU5Character
import GUT.Common.StandardChain.StandardChain

open Math

/-!
# A positive-target actual 27 model on the compact E6 candidate

The residual action is trivial and the concrete mass is zero. The target
is a derived dual chiral index, not the full light spectrum: the vectorlike
five/bar-five pair and two neutral singlets remain among the 27 zero modes.
No global E6 identification or nonzero decay amplitude is asserted.
-/

set_option autoImplicit false

namespace GUT.E6.MinusculeBenchmark

open Math.E6
noncomputable section

open Minuscule Minuscule.SU5Coordinates GUT.SU5
open InvariantWeylMass FiniteAbelianChargeSectors StandardAbelianCharge
open StandardSMCharacterTarget StandardWeylDualTarget

variable (H : Type*) [CommGroup H]

def rho : Representation ℂ (compactIdentityComponent × H) Hilbert27 :=
  representation.comp (MonoidHom.fst _ _)

theorem unitary : UnitaryMultiplicity.IsUnitaryRepresentation (rho H) :=
  fun g => representation_unitary g.1

@[simp] theorem residual_trivial (h : H) : rho H (1, h) = 1 :=
  map_one representation

def family : FiniteChargeProfiles.Family (ChargeLabel H) :=
  ⟨FiniteChargeProfiles.pure 1 (sectorCharges 0 0), 1, by decide,
    FiniteChargeProfiles.pure_totals _ _⟩

def singlets : ChargeLabel H →₀ ℤ := Finsupp.single 0 2

theorem target_eval (g : TorusCharacter.CombinedGroup H) :
    TorusCharacter.eval
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) g =
      2 + TorusCharacter.eval (exactSMResolvedCharacter 1 (sectorCharges 0 0)) g := by
  change TorusCharacter.eval (FiniteChargeProfiles.targetWithSinglets
    (FiniteChargeProfiles.pure 1 (sectorCharges 0 0)) (singlets H)) g = _
  rw [FiniteChargeProfiles.targetWithSinglets_pure, exactSMWithSingletsResolvedCharacter,
    ← TorusCharacter.evalAddHom_apply, map_add]
  simp only [TorusCharacter.evalAddHom_apply, singlets, singletResolvedCharacter,
    Finsupp.mapDomain_single, TorusCharacter.eval_single, Int.cast_ofNat]
  have hk : TorusCharacter.keyCharacter (0, (0 : ChargeLabel H)) g = 1 := by
    change (TorusCharacter.weightCharacter 0 g.1 : ℂ) * 1 = 1
    have hz : rawReducedWeight 0 = 0 := by ext i; fin_cases i <;> rfl
    simp [TorusCharacter.weightCharacter, TorusCharacter.rawCharacter, hz]
  rw [hk, mul_one, add_comm]
  simp only [Nat.cast_one]

theorem restricted_character (g : TorusCharacter.CombinedGroup H) :
    (rho H).character (inclusion (MaximalTorus.hom g.1), g.2) =
      TorusCharacter.eval
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) g +
      Matter.fundamental.character (MaximalTorus.hom g.1) +
      Matter.antifundamental.character (MaximalTorus.hom g.1) := by
  change representation.character (inclusion (MaximalTorus.hom g.1)) = _
  rw [su5_character, target_eval]
  have hp := TorusMatterCharacter.charged_pair_character (0 : ChargeLabel H) 0 g.1 g.2
  have hz (h : H) : ((0 : ChargeLabel H).toMul h : ℂ) = 1 := rfl
  simp only [hz, mul_one] at hp
  rw [← Representation.char_iso UnitaryMatter.tenEquiv,
    ← Representation.char_iso UnitaryMatter.antifundamentalEquiv] at hp
  rw [← hp]
  ring

theorem restricted_dual_index (g : TorusCharacter.CombinedGroup H) :
    (TorusCharacterSource.restrict (StandardChain.pullback inclusion (rho H))).character g -
      (TorusCharacterSource.restrict (StandardChain.pullback inclusion (rho H))).dual.character g =
      TorusCharacter.eval (chiralDifference
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H))) g := by
  rw [Representation.char_dual]
  change (rho H).character (inclusion (MaximalTorus.hom g.1), g.2) -
    (rho H).character (inclusion (MaximalTorus.hom g.1⁻¹), g.2⁻¹) = _
  rw [restricted_character H g, restricted_character H (g.1⁻¹, g.2⁻¹),
    TorusCharacter.eval_chiralDifference]
  simp only [Matter.antifundamental, Representation.char_dual, map_inv, inv_inv]
  ring_nf
  rfl

/-- Index conservation makes the target independent of the invariant mass.
The zero choice below is an inhabitant, not an assumption of this theorem. -/
theorem hasTarget (B : SymmetricMass (TorusCharacterSource.restrict
    (StandardChain.pullback inclusion (rho H)))) :
    TorusMassSource.HasTarget (StandardChain.pullback inclusion (rho H))
      B (family H).profiles (singlets H) :=
  fun g => (B.radical_dual_character_eq g).trans (restricted_dual_index H g)

def model : StandardChain.Model inclusion (rho H) where
  unitary := unitary H
  mass := SymmetricMass.zero _
  profile := family H
  singlets := singlets H
  lightTarget := hasTarget H _

theorem rho_continuous [TopologicalSpace H] :
    Continuous (fun p : (compactIdentityComponent × H) × Hilbert27 => rho H p.1 p.2) := by
  change Continuous (fun p : (compactIdentityComponent × H) × Hilbert27 =>
    representation p.1.1 p.2)
  have hc : Continuous (fun p : (compactIdentityComponent × H) × Hilbert27 => (p.1.1, p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  exact Continuous.comp (f := fun p : (compactIdentityComponent × H) × Hilbert27 =>
    (p.1.1, p.2)) (g := fun p : compactIdentityComponent × Hilbert27 => representation p.1 p.2)
    representation_continuous hc

def continuousModel [TopologicalSpace H] [IsTopologicalGroup H] :
    StandardChain.ContinuousModel inclusion (rho H) where
  toModel := model H
  inclusion_injective := inclusion_injective
  inclusion_continuous := inclusion_continuous
  action_continuous := rho_continuous H

theorem radical_top : (model H).mass.radical.toSubmodule = ⊤ :=
  SymmetricMass.radical_zero

theorem radical_finrank : Module.finrank ℂ (model H).mass.radical.toSubmodule = 27 := by
  rw [radical_top, finrank_top, hilbert27_finrank]

theorem target_eval_one : TorusCharacter.eval
    (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) 1 = 17 := by
  rw [target_eval]
  have hp := TorusMatterCharacter.charged_pair_character (0 : ChargeLabel H) 0 1 1
  have hs : TorusCharacter.eval (exactSMResolvedCharacter 1 (sectorCharges
      (0 : ChargeLabel H) 0)) (1 : TorusCharacter.CombinedGroup H) = 15 := by
    norm_num at hp
    exact hp.symm
  rw [hs]
  norm_num

/-- The dual target is deliberately not a full-spectrum assertion. -/
theorem radical_character_ne_target :
    ¬ (∀ g, (model H).mass.radical.toRepresentation.character g =
      TorusCharacter.eval
        (FiniteChargeProfiles.targetWithSinglets (family H).profiles (singlets H)) g) := by
  intro h
  have hi := h 1
  rw [Representation.char_one, radical_finrank, target_eval_one] at hi
  norm_num at hi

theorem light_dual_index : chiralDifference (model H).lightSpectrum =
    chiralDifference (FiniteChargeProfiles.targetWithSinglets
      (family H).profiles (singlets H)) :=
  TorusMassSource.chiral_spectrum (StandardChain.pullback inclusion (rho H))
    (StandardChain.pullback_unitary inclusion (rho H) (unitary H))
    (model H).mass _ _ (hasTarget H _)

theorem profile_at_smWeight (i : Fin 15) :
    StandardSMCharacterTarget.smCharge (family H).profiles i (0 : ChargeLabel H) = 1 := by
  fin_cases i <;> simp [family, FiniteChargeProfiles.pure,
    StandardSMCharacterTarget.smCharge, sectorCharges]

theorem light_index_coefficient (i : Fin 15) :
    chiralDifference (model H).lightSpectrum (smReducedWeight i, (0 : ChargeLabel H)) = 1 := by
  rw [light_dual_index, FiniteChargeProfiles.chiralDifference_target_apply,
    profile_at_smWeight, Nat.cast_one]

theorem exists_sm_zeroMode (i : Fin 15) :
    ∃ v : (model H).mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, (model H).mass.radical.toRepresentation g v =
        TorusCharacter.keyCharacter (smReducedWeight i, (0 : ChargeLabel H)) g • v := by
  apply TorusMassSource.exists_zeroMode _
    (StandardChain.pullback_unitary inclusion _ (model H).unitary)
    (model H).mass _ _ (model H).lightTarget i 0
  change 0 < StandardSMCharacterTarget.smCharge (family H).profiles i (0 : ChargeLabel H)
  rw [profile_at_smWeight]
  decide

theorem nonvacuous :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (model H).lightSpectrum := (model H).selection_rule_obstruction

end

end GUT.E6.MinusculeBenchmark
