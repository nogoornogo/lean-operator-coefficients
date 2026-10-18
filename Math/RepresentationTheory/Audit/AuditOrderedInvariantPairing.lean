import Math.RepresentationTheory.OrderedInvariantPairing
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Ordered pairing imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.OrderedInvariantPairing.swapMiddle,
    ``Math.OrderedInvariantPairing.coefficient_comp_equiv_ne_zero,
    ``Math.OrderedInvariantPairing.exists_ordered_coefficient,
    ``Math.OrderedInvariantPairing.exists_dual_first_coefficient]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Ordered pairing: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Ordered pairing: layer and {declarations.length} strict axiom checks passed"
