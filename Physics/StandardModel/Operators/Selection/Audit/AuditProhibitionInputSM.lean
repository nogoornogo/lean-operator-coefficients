import Physics.StandardModel.Operators.Selection.ProhibitionInputSM
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Prohibition input imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [``Physics.ProhibitionInputSM.Forbids,
    ``Physics.ProhibitionInputSM.AllForbids,
    ``Physics.ProhibitionInputSM.facade_iff,
    ``Physics.ProhibitionInputSM.residual_iff,
    ``Physics.ProhibitionInputSM.koren,
    ``Physics.ProhibitionInputSM.bgw,
    ``Physics.ProhibitionInputSM.dgt,
    ``Physics.ProhibitionInputSM.dgt_restriction,
    ``Physics.ProhibitionInputSM.quarticity_domains,
    ``Physics.ProhibitionInputSM.llhh_forbidden_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Prohibition input: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Prohibition input: {declarations.length} strict axiom checks passed"
