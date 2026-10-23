import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.HeeckLeDuqlCertificate
import Physics.StandardModel.Operators.BaryonOne.Qque.HeeckLeQqueCertificate
import Physics.StandardModel.Operators.BaryonOne.Qqql.HeeckLeQqqlCertificate
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.HeeckLeDuueCertificate
import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkResidual
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Strict transitive audits of every declaration in the comparison namespaces. -/
run_cmd do
  let env ← Lean.getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Heeck-Le imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let prefixes := [`Physics.HeeckLeDuqlCertificate, `Physics.HeeckLeQqueCertificate,
    `Physics.HeeckLeQqqlConvention, `Physics.HeeckLeQqqlCertificate,
    `Physics.HeeckLeDuueCertificate, `Physics.HeeckLeSixQuarkCertificate,
    `Physics.HeeckLeSixQuarkLocalBasis, `Physics.HeeckLeSixQuarkResidual]
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
