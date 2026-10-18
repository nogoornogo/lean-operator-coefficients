import Math.RepresentationTheory.Decomposition.CommonIrreducible
import Math.RepresentationTheory.Decomposition.SymmetricSquareSemisimple
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Common constituent imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.CommonIrreducible.nonzero_iff,
    ``Math.CommonIrreducible.all_zero_iff,
    ``Math.SymmetricSquareSemisimple.quotient_surjective,
    ``Math.SymmetricSquareSemisimple.of_tensor,
    ``Math.SymmetricSquareSemisimple.of_compact]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Common constituent algebra: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Common constituent algebra: {declarations.length} strict axiom checks passed"
