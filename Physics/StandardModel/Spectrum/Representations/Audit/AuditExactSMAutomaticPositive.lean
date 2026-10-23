import Physics.StandardModel.Spectrum.Representations.ExactSMAutomaticPositive
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Exact SM positive extraction imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.ExactSMAutomaticPositive.shared_positive,
    ``Physics.ExactSMAutomaticPositive.pairwise_positive]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exact SM positive extraction: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact SM positive extraction: {declarations.length} strict axiom checks passed"
