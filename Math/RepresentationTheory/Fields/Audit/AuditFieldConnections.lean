import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Fields.Controls
import Math.RepresentationTheory.Fields.JetConnection
import Lean.Util.CollectAxioms

/-! Every declaration owned by the shared field-connection modules, including
private/generated declarations, is checked transitively. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Shared field connection imports upper layer {mod}"
  let owned := #[`Math.RepresentationTheory.Fields.Selection,
    `Math.RepresentationTheory.Fields.Interactions,
    `Math.RepresentationTheory.Fields.DerivativeConnection,
    `Math.RepresentationTheory.Fields.JetConnection,
    `Math.RepresentationTheory.Fields.Controls]
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if let some i := env.getModuleIdxFor? d then
      let mod := env.header.moduleNames[i]!
      if owned.contains (SourceLayout.originalModule mod) then
        checked := checked + 1
        for ax in (← collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Field connection {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Shared field connection inventory is empty"
  logInfo m!"Shared field connections: {checked} strict transitive checks passed"
