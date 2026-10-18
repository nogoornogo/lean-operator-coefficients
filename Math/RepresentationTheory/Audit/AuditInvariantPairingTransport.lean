import Math.RepresentationTheory.InvariantPairingTransport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Transport assumptions remain explicit, including surjectivity and nonzero targets. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Pairing transport imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.InvariantPairing.pulledCoefficient,
    ``Math.InvariantPairing.pulledCoefficient_apply,
    ``Math.InvariantPairing.exists_pulledCoefficient_eq_one,
    ``Math.InvariantPairing.pulledCoefficient_ne_zero,
    ``Math.InvariantPairing.pulledCoefficient_zero_first]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Pairing transport: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Pairing transport: layer and {declarations.length} strict axiom checks passed"
