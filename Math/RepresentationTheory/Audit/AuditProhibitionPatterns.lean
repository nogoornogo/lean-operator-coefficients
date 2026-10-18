import Math.RepresentationTheory.ProhibitionPatterns
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Prohibition patterns imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ProhibitionPatterns.cyclic_forbidden_iff,
    ``Math.ProhibitionPatterns.cyclic_neutral_allowed]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Prohibition patterns: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Prohibition patterns: {ds.length} strict transitive checks passed"
