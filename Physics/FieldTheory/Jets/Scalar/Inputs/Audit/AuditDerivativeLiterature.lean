import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureMixed

/-! Persistent strict transitive audits; Physics may not import GUT. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let owned := [`Physics.DerivativeLiteratureScalar, `Physics.DerivativeLiteratureMixed]
  let mut checked : Nat := 0
  for (d, _) in env.constants.toList do
    if owned.any (fun ns => ns.isPrefixOf d) then
      checked := checked + 1
      for ax in (← Lean.collectAxioms d) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Declaration {d} uses unexpected axiom {ax}"
  unless checked > 0 do
    throwError "Derivative comparison inventory is empty"
  Lean.logInfo m!"Derivative literature Physics: {checked} strict transitive declaration checks passed"
