import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Coefficients.ScalarCompletenessChecks

/-! Strict inventory of all new C1 consumer declarations. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let mut checked : Nat := 0
  for (d, _) in env.constants.toList do
    if (`Math.ScalarCompletenessChecks).isPrefixOf d then
      checked := checked + 1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do
    throwError "C1 consumer inventory is empty"
  Lean.logInfo m!"Scalar completeness Math consumers: {checked} strict transitive checks passed"
