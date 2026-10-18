import Math.RepresentationTheory.Decomposition.FiniteIrreducibleQuotient
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Finite irreducible quotient imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.FiniteIrreducibleQuotient.exists_split,
    ``Math.FiniteIrreducibleQuotient.blockProjection_surjective,
    ``Math.FiniteIrreducibleQuotient.exists_irreducible_quotient]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite irreducible quotient: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite irreducible quotient: layer and {declarations.length} strict axiom checks passed"
