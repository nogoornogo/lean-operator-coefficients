import Math.Audit.ImportOrigin
import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseMoments
import Math.Algebra.HiggsFourWaveCubature.Structural.SecondCollinear

/-! Strict transitive axiom and layer inventory, including private structural helpers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Math.Algebra.HiggsFourWaveCubature.Structural).isPrefixOf env.header.moduleNames[idx.toNat]! then
        checked := checked + 1
        for ax in (← Lean.collectAxioms name) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {name} uses unexpected axiom {ax}"
  unless checked > 0 do throwError "Empty structural cubature inventory"
  Lean.logInfo m!"All cubature families: {checked} strict transitive declaration checks passed"
