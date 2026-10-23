import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourSeparation

/-! Strict inventories of actual Higgs input, relations and quotient separators. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Physics.HiggsQuarticFourInput, `Physics.HiggsQuarticFourWaves,
      `Physics.HiggsQuarticFourSeparation] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do throwError "Empty Higgs order-four inventory: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
