import Math.RepresentationTheory.InvariantPairing
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Strict axiom and layer audit for group-independent evaluation coefficients. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Invariant pairing imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.InvariantPairing.evaluation,
    ``Math.InvariantPairing.pairedCoefficient,
    ``Math.InvariantPairing.pairedCoefficient_apply,
    ``Math.InvariantPairing.pairedCoefficient_invariant,
    ``Math.InvariantPairing.exists_pairedCoefficient_eq_one,
    ``Math.InvariantPairing.pairedCoefficient_ne_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Invariant pairing: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Invariant pairing: layer and {declarations.length} strict axiom checks passed"
