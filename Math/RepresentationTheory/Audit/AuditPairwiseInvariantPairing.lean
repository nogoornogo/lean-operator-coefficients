import Math.RepresentationTheory.PairwiseInvariantPairing
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Pairwise invariant pairing imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.PairwiseInvariantPairing.coefficient,
    ``Math.PairwiseInvariantPairing.apply_coefficient,
    ``Math.PairwiseInvariantPairing.swap,
    ``Math.PairwiseInvariantPairing.diagonal,
    ``Math.PairwiseInvariantPairing.exists_common_vector,
    ``Math.PairwiseInvariantPairing.exists_diagonal,
    ``Math.PairwiseInvariantPairing.coefficient_nonzero,
    ``Math.PairwiseInvariantPairing.same_quotient]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Pairwise invariant pairing: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Pairwise invariant pairing: {declarations.length} strict axiom checks passed"
