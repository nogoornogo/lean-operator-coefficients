import Math.Audit.ImportOrigin
import Math.Algebra.Constructions.ScalarDegreeFour
import Math.Algebra.Waves.FourWavePolarization
import Math.Algebra.Waves.ScalarFourWaveCubature

/-! Strict source-layer and transitive axiom inventory for finite quartic helpers. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  for ns in [`Math.ScalarDegreeFour, `Math.FourWavePolarization, `Math.ScalarFourWaveCubature] do
    let mut checked : Nat := 0
    for (d, _) in env.constants.toList do
      if ns.isPrefixOf d then
        checked := checked + 1
        for ax in (← Lean.collectAxioms d) do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Declaration {d} uses unexpected axiom {ax}"
    unless checked > 0 do
      throwError "Empty quartic Math inventory: {ns}"
    Lean.logInfo m!"{ns}: {checked} strict transitive declaration checks passed"
