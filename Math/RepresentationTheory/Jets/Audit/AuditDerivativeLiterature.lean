import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Jets.DerivativeLiteratureScalar
import Math.RepresentationTheory.Jets.DerivativeLiteratureHiggs

/-! Persistent strict transitive audits of the bounded comparison sources. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Math.DerivativeLiteratureScalar, `Math.DerivativeLiteratureHiggs]
  let mut checked : Nat := 0
  for (d, _) in env.constants.toList do
    if owned.any (fun ns => ns.isPrefixOf d) then
      checked := checked + 1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do
    throwError "Derivative comparison inventory is empty"
  Lean.logInfo m!"Derivative literature Math: {checked} strict transitive declaration checks passed"
