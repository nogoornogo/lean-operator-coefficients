import Physics.StandardModel.Gauge.Tensors.LightSMAction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace Physics.LightSMActionAudit
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
end Physics.LightSMActionAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Light SM action imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.LightSMAction.Compatible,
    ``Physics.LightSMAction.residual_agrees,
    ``Physics.LightSMAction.residual_restriction,
    ``Physics.LightSMAction.dual_restriction,
    ``Physics.LightSMAction.dual_residual_restriction,
    ``Physics.LightSMAction.ofDecomposition,
    ``Physics.LightSMAction.ofPreservesRadical,
    ``Physics.LightSMAction.ofPreservesRadical_apply,
    ``Physics.LightSMAction.massForAction_form,
    ``Physics.LightSMAction.massForAction_radical,
    ``Physics.LightSMAction.preservesRadical_of_invariant,
    ``Physics.LightSMAction.ofInvariantMass,
    ``Physics.LightSMAction.ofPreservesRadical_continuous,
    ``Physics.LightSMAction.ofInvariantMass_continuous,
    ``Physics.LightSMAction.dual_continuous,
    ``Physics.LightSMActionAudit.zeroAction,
    ``Physics.LightSMActionAudit.zero_action_continuous,
    ``Physics.LightSMActionAudit.zero_action_carrier,
    ``Physics.LightSMActionAudit.unitMass_nonzero,
    ``Physics.LightSMActionAudit.unitAction,
    ``Physics.LightSMActionAudit.unit_action_continuous]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Light SM action: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Light SM action: {declarations.length} strict axiom checks passed"
