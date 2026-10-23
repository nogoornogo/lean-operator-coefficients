import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Lagrangian.LagrangianHelper

/-! Strict transitive audit of the actual Lorentz consumer. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let mut checked : Nat := 0
  for (d, _) in env.constants.toList do
    if (`Physics.ScalarLagrangianHelper).isPrefixOf d then
      checked := checked + 1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do
    throwError "Lorentz Lagrangian helper audit inventory is empty"
  Lean.logInfo m!"Lorentz Lagrangian helper: {checked} strict transitive declaration checks passed"
