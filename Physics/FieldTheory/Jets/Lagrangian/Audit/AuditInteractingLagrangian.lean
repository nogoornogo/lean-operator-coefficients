import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Lagrangian.InteractingLagrangianLiterature

/-! Strict audit of the physical-source comparison consumers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected GUT import {mod}; original {SourceLayout.originalModule mod}"
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if (`Physics.InteractingLagrangianLiterature).isPrefixOf d then
      checked := checked+1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Interacting literature audit inventory is empty"
  Lean.logInfo m!"Interacting literature: {checked} strict transitive checks passed"
