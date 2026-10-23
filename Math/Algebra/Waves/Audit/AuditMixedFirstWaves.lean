import Math.Audit.ImportOrigin
import Math.Algebra.Jets.MixedFirstJetWords
import Math.Algebra.Waves.MixedFourWaveEvaluation

/-! Strict transitive inventory of the resumed mixed-source foundations. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Math.MixedFirstJetWords, `Math.MixedFourWaveEvaluation,
      `Math.MixedJetConstantOdd, `Math.TwoSidedDifferential] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do throwError "Empty mixed-wave inventory: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
