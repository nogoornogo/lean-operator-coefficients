import Physics.StandardModel.Operators.Support.Quark.SMQLPatternRequests
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "q/l pattern facade audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMQLPatternRequests.selector_matches_existing,
    ``Physics.SMQLPatternRequests.entry_original, ``Physics.SMQLPatternRequests.allowed_iff_original,
    ``Physics.SMQLPatternRequests.forbidden_iff_original, ``Physics.SMQLPatternRequests.entry_allowed_iff,
    ``Physics.SMQLPatternRequests.allowed_iff, ``Physics.SMQLPatternRequests.forbidden_iff,
    ``Physics.SMQLPatternRequests.forbid_of_charge, ``Physics.SMQLPatternRequests.satisfies_iff,
    ``Physics.SMQLPatternRequests.original_request_iff, ``Physics.SMQLPatternRequests.b1_b2_iff,
    ``Physics.SMQLPatternRequests.b1_b2_original_iff, ``Physics.SMQLPatternRequests.allow_of_entry]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "q/l pattern facade audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"q/l pattern facade audit: layer and {ds.length} strict transitive checks passed; extraction consumers remain conditional"
