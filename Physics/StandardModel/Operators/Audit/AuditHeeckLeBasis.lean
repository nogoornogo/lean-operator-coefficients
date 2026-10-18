import Physics.StandardModel.Operators.HeeckLeDuqlCertificate
import Physics.StandardModel.Operators.HeeckLeQqueCertificate
import Physics.StandardModel.Operators.HeeckLeQqqlCertificate
import Physics.StandardModel.Operators.HeeckLeDuueCertificate
import Physics.StandardModel.Operators.HeeckLeSixQuarkResidual
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Strict transitive audits of every declaration in the comparison namespaces. -/
run_cmd do
  let env ← Lean.getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Heeck-Le imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let prefixes := [`GUT.HeeckLeDuqlCertificate, `GUT.HeeckLeQqueCertificate,
    `GUT.HeeckLeQqqlConvention, `GUT.HeeckLeQqqlCertificate,
    `GUT.HeeckLeDuueCertificate, `GUT.HeeckLeSixQuarkCertificate,
    `GUT.HeeckLeSixQuarkLocalBasis, `GUT.HeeckLeSixQuarkResidual]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Heeck-Le {name} uses unexpected axiom {ax}"
      count := count + 1
  if count < 50 then
    throwError "Heeck-Le audit unexpectedly found only {count} declarations"
  Lean.logInfo m!"Heeck-Le: {count} strict transitive axiom checks passed"
