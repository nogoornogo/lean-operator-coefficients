import Physics.StandardModel.Gauge.LightSMAction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.LightSMActionAudit
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open SU5.MaximalTorus

abbrev source := Representation.trivial ℂ (Torus × Circle) ℂ
abbrev gauge := Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × Circle) ℂ

def zeroAction : LightSMAction.Compatible (MonoidHom.id Torus) source
    (SymmetricMass.zero (source.comp ((MonoidHom.id Torus).prodMap (MonoidHom.id Circle)))) :=
  LightSMAction.ofInvariantMass _ _ _ gauge (by intros; rfl) (by ext; rfl)

theorem zero_action_continuous : IsJointlyContinuous zeroAction.action :=
  LightSMAction.ofInvariantMass_continuous _ _ _ gauge _ _ continuous_snd

theorem zero_action_carrier : Module.finrank ℂ
    (SymmetricMass.zero (source.comp ((MonoidHom.id Torus).prodMap
      (MonoidHom.id Circle)))).radical.toSubmodule = 1 := by
  rw [(SymmetricMass.zeroRadicalEquiv _).toLinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

def unitMass : SymmetricMass
    (source.comp ((MonoidHom.id Torus).prodMap (MonoidHom.id Circle))) where
  form := LinearMap.mul ℂ ℂ
  symmetric := ⟨mul_comm⟩
  invariant _ _ _ := rfl

theorem unitMass_nonzero : unitMass.form ≠ 0 := by
  intro he
  have hh := LinearMap.congr_fun (LinearMap.congr_fun he 1) 1
  norm_num [unitMass] at hh

def unitAction : LightSMAction.Compatible (MonoidHom.id Torus) source unitMass :=
  LightSMAction.ofInvariantMass _ _ _ gauge (by intros; rfl) (by ext; rfl)

theorem unit_action_continuous : IsJointlyContinuous unitAction.action :=
  LightSMAction.ofInvariantMass_continuous _ _ _ gauge _ _ continuous_snd

end
end GUT.LightSMActionAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Light SM action imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.LightSMAction.Compatible,
    ``GUT.LightSMAction.residual_agrees,
    ``GUT.LightSMAction.residual_restriction,
    ``GUT.LightSMAction.dual_restriction,
    ``GUT.LightSMAction.dual_residual_restriction,
    ``GUT.LightSMAction.ofDecomposition,
    ``GUT.LightSMAction.ofPreservesRadical,
    ``GUT.LightSMAction.ofPreservesRadical_apply,
    ``GUT.LightSMAction.massForAction_form,
    ``GUT.LightSMAction.massForAction_radical,
    ``GUT.LightSMAction.preservesRadical_of_invariant,
    ``GUT.LightSMAction.ofInvariantMass,
    ``GUT.LightSMAction.ofPreservesRadical_continuous,
    ``GUT.LightSMAction.ofInvariantMass_continuous,
    ``GUT.LightSMAction.dual_continuous,
    ``GUT.LightSMActionAudit.zeroAction,
    ``GUT.LightSMActionAudit.zero_action_continuous,
    ``GUT.LightSMActionAudit.zero_action_carrier,
    ``GUT.LightSMActionAudit.unitMass_nonzero,
    ``GUT.LightSMActionAudit.unitAction,
    ``GUT.LightSMActionAudit.unit_action_continuous]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Light SM action: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Light SM action: {declarations.length} strict axiom checks passed"
