import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureRecheck

/-! Persistent strict inventory of every renewed literature consumer. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected model-layer source {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Physics.DerivativeLiteratureRecheck.C1, `Physics.DerivativeLiteratureRecheck.C2,
      `Physics.DerivativeLiteratureRecheck.C3, `Physics.DerivativeLiteratureRecheck.C4,
      `Physics.DerivativeLiteratureRecheck.C5, `Physics.DerivativeLiteratureRecheck.C6] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Literature recheck inventory is empty: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
