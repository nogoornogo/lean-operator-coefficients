import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Lagrangian.LagrangianModelLiterature
import Physics.FieldTheory.Jets.Lagrangian.YukawaModelControls

/-! Strict transitive audit of registered models, Yukawa symmetry and source
consumers, with the Physics/GUT import boundary unchanged. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected GUT import {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Physics.YukawaModel, `Physics.YukawaModelControls,
    `Physics.RegisteredLagrangianModels, `Physics.LagrangianModelLiterature]
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if owned.any (fun ns => ns.isPrefixOf d) then
      checked := checked+1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Physical model audit inventory is empty"
  Lean.logInfo m!"Lagrangian physical models: {checked} strict transitive checks passed"
