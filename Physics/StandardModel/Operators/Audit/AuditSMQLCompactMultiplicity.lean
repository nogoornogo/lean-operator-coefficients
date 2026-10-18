import Physics.StandardModel.Operators.SMQLCompactMultiplicity
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "q/l compact extraction audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMQLCompactMultiplicity.test_allowed_iff,
    ``GUT.SMQLCompactMultiplicity.original_allowed_iff,
    ``GUT.SMQLCompactMultiplicity.original_forbidden_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "q/l compact extraction audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"q/l compact extraction audit: layer and {ds.length} strict transitive conditional checks passed"
