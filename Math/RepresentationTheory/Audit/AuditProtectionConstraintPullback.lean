import Math.RepresentationTheory.ProtectionConstraintPullback
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod then
      throwError "Unexpected upper-layer import: {mod}"
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected upper-layer import: {mod}"
    let origin := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf origin || (`GUT.SU6).isPrefixOf origin then
      throwError "Unexpected original unified-model import: {mod}"
  let ds := [``Math.ProtectionConstraintPullback.retain,
    ``Math.ProtectionConstraintPullback.preserve,
    ``Math.ProtectionConstraintPullback.exclude,
    ``Math.ProtectionConstraintPullback.keep_outside,
    ``Math.ProtectionConstraintPullback.finiteCandidates,
    ``Math.ProtectionConstraintPullback.mem_finiteCandidates,
    ``Math.ProtectionConstraintPullback.ScalarAdmission,
    ``Math.ProtectionConstraintPullback.cyclic_necessary,
    ``Math.ProtectionConstraintPullback.cyclic_retain,
    ``Math.ProtectionConstraintPullback.neutral_excludes,
    ``Math.ProtectionConstraintPullback.neutral_line_not_forbidden,
    ``Math.ProtectionConstraintPullback.zero_domain_control]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Constraint pullback: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Constraint pullback: {ds.length} strict transitive checks passed"
