import Math.Audit.ImportOrigin
import GUT.SU6.Boundary.FieldConnection
import Lean.Util.CollectAxioms

/-! All declarations of the constructed gauge/residual boundary dictionaries. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (d,_) in env.constants.toList do
    if let some i := env.getModuleIdxFor? d then
      let mod := env.header.moduleNames[i]!
      if SourceLayout.originalModule mod == `GUT.SU6.Boundary.FieldConnection then
        checked := checked + 1
        for ax in (← collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "SU6 field connection {d} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "SU6 field connection inventory is empty"
  logInfo m!"SU6 field connection: {checked} strict transitive checks passed"
