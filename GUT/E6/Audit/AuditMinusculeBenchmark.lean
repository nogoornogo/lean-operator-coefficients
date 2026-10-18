import GUT.E6.SelectionRules.MinusculeBenchmark
import Lean.Util.CollectAxioms

open Math

/-! Actual finite and continuous residual-group examples on the candidate
27. Positive orientation and the distinction between the full spectrum
and its dual index are checked, without a global E6 identification. -/

set_option autoImplicit false

namespace GUT.E6.AuditMinusculeBenchmark

open Math.E6
noncomputable section

open Minuscule Minuscule.SU5Coordinates MinusculeBenchmark GUT.SU5
open FiniteAbelianChargeSectors StandardAbelianCharge StandardSMCharacterTarget
open StandardWeylDualTarget

abbrev FiniteResidual := Multiplicative (ZMod 3)

local instance : TopologicalSpace FiniteResidual := ⊥
local instance : DiscreteTopology FiniteResidual := ⟨rfl⟩

def finiteModel := model FiniteResidual
def finiteContinuousModel := continuousModel FiniteResidual
def circleModel := continuousModel Circle

theorem positive_finite_example :
    finiteModel.profile.generations = 1 ∧
      Module.finrank ℂ finiteModel.mass.radical.toSubmodule = 27 ∧
      ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
        finiteModel.lightSpectrum :=
  ⟨rfl, radical_finrank _, nonvacuous _⟩

theorem positive_circle_example :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      circleModel.toModel.lightSpectrum := circleModel.selection_rule_obstruction

theorem physical_target (z : PhysicalTorus.Coordinates) (h : Circle) :
    circleModel.toModel.mass.radical.toRepresentation.character (PhysicalTorus.toTorus z, h) -
        circleModel.toModel.mass.radical.toRepresentation.dual.character
          (PhysicalTorus.toTorus z, h) =
      TorusCharacter.eval (chiralDifference (FiniteChargeProfiles.targetWithSinglets
        (family Circle).profiles (singlets Circle))) (PhysicalTorus.toTorus z, h) :=
  circleModel.toModel.lightTarget _

theorem not_zero_generation : chiralDifference finiteModel.lightSpectrum ≠ 0 := by
  intro h
  have hp := light_index_coefficient FiniteResidual 0
  change chiralDifference finiteModel.lightSpectrum _ = 1 at hp
  rw [h] at hp
  norm_num at hp

theorem not_negative_orientation :
    chiralDifference finiteModel.lightSpectrum ≠
      -chiralDifference (FiniteChargeProfiles.targetWithSinglets
        (family FiniteResidual).profiles (singlets FiniteResidual)) := by
  intro h
  have hp := congrArg (fun p : ResolvedCharacter (ChargeLabel FiniteResidual) =>
    p (smReducedWeight 0, 0)) h
  dsimp only [finiteModel] at hp
  rw [light_index_coefficient, Finsupp.neg_apply,
    FiniteChargeProfiles.chiralDifference_target_apply, profile_at_smWeight] at hp
  norm_num at hp

theorem actual_modes (i : Fin 15) :
    ∃ v : finiteModel.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, finiteModel.mass.radical.toRepresentation g v =
        TorusCharacter.keyCharacter (smReducedWeight i, (0 : ChargeLabel FiniteResidual)) g • v :=
  exists_sm_zeroMode _ i

example : ¬ (∀ g, finiteModel.mass.radical.toRepresentation.character g =
    TorusCharacter.eval (FiniteChargeProfiles.targetWithSinglets
      (family FiniteResidual).profiles (singlets FiniteResidual)) g) :=
  radical_character_ne_target _

example (h : FiniteResidual) : rho FiniteResidual (1, h) = 1 := residual_trivial _ h

example : Continuous (fun p : (SU5Coordinates.SU5 × Circle) × Hilbert27 =>
    StandardChain.pullback inclusion (rho Circle) p.1 p.2) := circleModel.pullback_continuous

end

end GUT.E6.AuditMinusculeBenchmark

run_cmd do
  let declarations := [
    ``GUT.E6.Minuscule.representation,
    ``GUT.E6.Minuscule.representation_unitary,
    ``GUT.E6.Minuscule.representation_continuous,
    ``GUT.E6.Minuscule.hilbert27_finrank,
    ``GUT.E6.Minuscule.su5RestrictionEquiv,
    ``GUT.E6.Minuscule.model_character,
    ``GUT.E6.Minuscule.su5_character,
    ``GUT.E6.Minuscule.su5_dual_index,
    ``GUT.E6.MinusculeBenchmark.unitary,
    ``GUT.E6.MinusculeBenchmark.residual_trivial,
    ``GUT.E6.MinusculeBenchmark.target_eval,
    ``GUT.E6.MinusculeBenchmark.restricted_character,
    ``GUT.E6.MinusculeBenchmark.restricted_dual_index,
    ``GUT.E6.MinusculeBenchmark.hasTarget,
    ``GUT.E6.MinusculeBenchmark.model,
    ``GUT.E6.MinusculeBenchmark.rho_continuous,
    ``GUT.E6.MinusculeBenchmark.continuousModel,
    ``GUT.E6.MinusculeBenchmark.radical_top,
    ``GUT.E6.MinusculeBenchmark.radical_finrank,
    ``GUT.E6.MinusculeBenchmark.target_eval_one,
    ``GUT.E6.MinusculeBenchmark.radical_character_ne_target,
    ``GUT.E6.MinusculeBenchmark.light_dual_index,
    ``GUT.E6.MinusculeBenchmark.light_index_coefficient,
    ``GUT.E6.MinusculeBenchmark.exists_sm_zeroMode,
    ``GUT.E6.MinusculeBenchmark.nonvacuous,
    ``GUT.E6.AuditMinusculeBenchmark.finiteContinuousModel,
    ``GUT.E6.AuditMinusculeBenchmark.circleModel,
    ``GUT.E6.AuditMinusculeBenchmark.positive_finite_example,
    ``GUT.E6.AuditMinusculeBenchmark.positive_circle_example,
    ``GUT.E6.AuditMinusculeBenchmark.physical_target,
    ``GUT.E6.AuditMinusculeBenchmark.not_zero_generation,
    ``GUT.E6.AuditMinusculeBenchmark.not_negative_orientation,
    ``GUT.E6.AuditMinusculeBenchmark.actual_modes]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 positive target: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 positive target: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 positive target: checked {declarations.length} declarations"
