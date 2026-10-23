import Math.RepresentationTheory.Constructions.JointSourceReexpression
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "reexpression Math audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.JointSourcePresentation.reexpress, ``Math.JointSourcePresentation.reexpress_expression]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "reexpression audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"reexpression: {ds.length} strict transitive checks passed"
