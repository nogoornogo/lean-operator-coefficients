import Math.RepresentationTheory.Characters.CompactWeylExtraction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Weyl extraction audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.CompactWeylExtraction.a2_formula, ``Math.CompactWeylExtraction.intCast_extractAt,
    ``Math.CompactWeylExtraction.intCast_constantTerm, ``Math.CompactWeylExtraction.coefficient_dimension]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weyl extraction audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weyl extraction audit: layer and {ds.length} strict transitive conditional checks passed"
