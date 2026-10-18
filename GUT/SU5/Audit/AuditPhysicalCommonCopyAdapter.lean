import GUT.SU5.SelectionRules.PhysicalCommonCopyAdapter
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT.SU6).isPrefixOf (SourceLayout.originalModule mod) then
      throwError "Unexpected original SU6 dependency: {mod}"
  let declarations := [
    ``GUT.SU5.PhysicalCommonCopyAdapter.sourceEmbedding,
    ``GUT.SU5.PhysicalCommonCopyAdapter.targetEmbedding,
    ``GUT.SU5.PhysicalCommonCopyAdapter.source_injective,
    ``GUT.SU5.PhysicalCommonCopyAdapter.realization,
    ``GUT.SU5.PhysicalCommonCopyAdapter.model,
    ``GUT.SU5.PhysicalCommonCopyAdapter.arbitrary_mass_light_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"PhysicalCommonCopyAdapter: {declarations.length} strict transitive axiom checks passed"
