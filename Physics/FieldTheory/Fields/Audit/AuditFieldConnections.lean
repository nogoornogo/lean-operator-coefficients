import Math.Audit.ImportOrigin
import Physics.FieldTheory.Fields.SelectionControls
import Physics.StandardModel.Spectrum.Representations.LeptonParityFieldConnection
import Physics.StandardModel.Operators.BaryonOne.Qque.S3FieldConnection
import Lean.Util.CollectAxioms

/-! All declarations of the physical factories and named model consumers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then throwError "Physical field connection imports GUT {mod}"
  let owned := #[`Physics.FieldTheory.Fields.SelectedFields,
    `Physics.FieldTheory.Fields.SelectionControls,
    `Physics.FieldTheory.Jets.Lagrangian.FieldInputConnection,
    `Physics.StandardModel.Spectrum.Representations.LeptonParityFieldConnection,
    `Physics.StandardModel.Operators.BaryonOne.Qque.S3FieldConnection]
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if let some i := env.getModuleIdxFor? d then
      let mod := env.header.moduleNames[i]!
      if owned.contains (SourceLayout.originalModule mod) then
        checked := checked + 1
        for ax in (← collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Physical field connection {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Physical field connection inventory is empty"
  logInfo m!"Physical field connections: {checked} strict transitive checks passed"
