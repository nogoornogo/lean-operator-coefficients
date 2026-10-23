import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkMatrix
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Audit every declaration, including private helpers, owned by the new
independent source/block modules. The old data/basis modules cannot be premises. -/
run_cmd do
  let env ← Lean.getEnv
  let modules := [
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkRecipe,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkBlocks,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkQuotient,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairSolvers,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkSupport,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkAssemblyBase,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkQuotientConnection,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairCoordinates,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairConnection,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkCouplingConnection,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkExtraction,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkMatrix]
  let banned := [
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkData,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkConvention,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkCertificate,
    `Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkLocalBasis,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFiniteData,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitData,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkCertificate,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalBasis]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "Structural Heeck-Le source module missing: {mod}"
  for mod in env.header.moduleNames do
    if banned.contains mod || (`GUT).isPrefixOf mod then
      throwError "Structural Heeck-Le imports excluded module {mod}; original {SourceLayout.originalModule mod}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[idx.toNat]! do continue
    for ax in (← Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Structural Heeck-Le {name} uses unexpected axiom {ax}"
    count := count+1
  if count < 80 then
    throwError "Structural Heeck-Le unexpectedly found only {count} declarations"
  Lean.logInfo m!"Structural Heeck-Le: {count} strict checks including private helpers; old data/basis imports absent"
