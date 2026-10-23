import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourUpper
import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourChecks

/-! Strict inventory of the complete source and invariant coefficient upper bound. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Physics.LorentzRankFour, `Physics.ScalarQuarticFourTensors,
      `Physics.ScalarQuarticFourSource, `Physics.ScalarQuarticFourUpper,
      `Physics.ScalarQuarticFourWaves, `Physics.ScalarQuarticFourCompleteness, `Physics.ScalarQuarticFourChecks] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Empty quartic Physics inventory: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
