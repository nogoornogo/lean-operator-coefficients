import Physics.StandardModel.Operators.SMQLPatternRequests
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "q/l pattern facade audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMQLPatternRequests.selector_matches_existing,
    ``GUT.SMQLPatternRequests.entry_original, ``GUT.SMQLPatternRequests.allowed_iff_original,
    ``GUT.SMQLPatternRequests.forbidden_iff_original, ``GUT.SMQLPatternRequests.entry_allowed_iff,
    ``GUT.SMQLPatternRequests.allowed_iff, ``GUT.SMQLPatternRequests.forbidden_iff,
    ``GUT.SMQLPatternRequests.forbid_of_charge, ``GUT.SMQLPatternRequests.satisfies_iff,
    ``GUT.SMQLPatternRequests.original_request_iff, ``GUT.SMQLPatternRequests.b1_b2_iff,
    ``GUT.SMQLPatternRequests.b1_b2_original_iff, ``GUT.SMQLPatternRequests.allow_of_entry]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "q/l pattern facade audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"q/l pattern facade audit: layer and {ds.length} strict transitive checks passed; extraction consumers remain conditional"
