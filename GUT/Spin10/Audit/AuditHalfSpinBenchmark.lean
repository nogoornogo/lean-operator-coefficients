import Math.Audit.ImportOrigin
import GUT.Spin10.SelectionRules.HalfSpinBenchmark

open Math

/-! Actual finite and continuous residual-group inhabitants, positive
orientation, physical-torus compatibility, and support on nonzero modes.
This is a zero-mass control, not a realistic mass or vacuum construction. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod || (`GUT.SUN.ProtonStabilityNoGo).isPrefixOf mod ||
        (`GUT.Sp).isPrefixOf mod then
      throwError "Half-spin benchmark imports another ambient model: {mod}"

namespace GUT.CompactSpin.AuditHalfSpinBenchmark

open Math.CompactSpin
noncomputable section

open HalfSpinBenchmark GUT.SU5 FiniteAbelianChargeSectors
open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget

abbrev FiniteResidual := Multiplicative (ZMod 3)

local instance : TopologicalSpace FiniteResidual := ⊥
local instance : DiscreteTopology FiniteResidual := ⟨rfl⟩

def finiteModel := model FiniteResidual

def finiteContinuousModel := continuousModel FiniteResidual

def circleModel := continuousModel Circle

theorem positive_finite_example :
    finiteModel.profile.generations = 1 ∧
      Module.finrank ℂ finiteModel.mass.radical.toSubmodule = 16 ∧
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

theorem singlet_is_present : finiteModel.lightSpectrum (0, (0 : ChargeLabel FiniteResidual)) = 1 :=
  light_singlet_coefficient _

/-- A zero-mass singlet is present but makes no contribution to the dual index. -/
theorem singlet_dual_index_zero :
    chiralDifference finiteModel.lightSpectrum (0, (0 : ChargeLabel FiniteResidual)) = 0 := by
  simp [chiralDifference]

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

example (h : FiniteResidual) : rho FiniteResidual (1, h) = 1 := residual_trivial _ h

example : Continuous (fun p : (SU5 × Circle) × Space =>
    GUT.StandardChain.pullback SU5Inclusion (rho Circle) p.1 p.2) :=
  circleModel.pullback_continuous

#print axioms HalfSpinBenchmark.unitary
#print axioms TorusMassSource.spectrum_eq_of_character
#print axioms residual_trivial
#print axioms target_eval
#print axioms restricted_character
#print axioms restricted_dual_index
#print axioms hasTarget
#print axioms model
#print axioms rho_continuous
#print axioms continuousModel
#print axioms radical_top
#print axioms radical_finrank
#print axioms radicalEquiv
#print axioms radical_character
#print axioms lightSpectrum_eq
#print axioms light_index_coefficient
#print axioms light_singlet_coefficient
#print axioms exists_sm_zeroMode
#print axioms nonvacuous
#print axioms positive_finite_example
#print axioms positive_circle_example
#print axioms physical_target
#print axioms singlet_dual_index_zero
#print axioms not_zero_generation
#print axioms not_negative_orientation
#print axioms actual_modes
#print axioms finiteContinuousModel
#print axioms circleModel

end

end GUT.CompactSpin.AuditHalfSpinBenchmark
