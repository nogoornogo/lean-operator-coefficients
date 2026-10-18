import Physics.StandardModel.Operators.HeeckLeSixQuarkMatrix
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Audit every declaration, including private helpers, owned by the new
independent source/block modules. The old data/basis modules cannot be premises. -/
run_cmd do
  let env ← Lean.getEnv
  let modules := [
    `Physics.StandardModel.Operators.HeeckLeSixQuarkRecipe,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkBlocks,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkQuotient,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkPairSolvers,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkSupport,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkAssemblyBase,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkQuotientConnection,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkPairCoordinates,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkPairConnection,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkCouplingConnection,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkExtraction,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkMatrix]
  let banned := [
    `Physics.StandardModel.Operators.HeeckLeSixQuarkData,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkConvention,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkCertificate,
    `Physics.StandardModel.Operators.HeeckLeSixQuarkLocalBasis,
    `Physics.StandardModel.Operators.LiSixQuarkFiniteData,
    `Physics.StandardModel.Operators.LiSixQuarkOrbitData,
    `Physics.StandardModel.Operators.LiSixQuarkCertificate,
    `Physics.StandardModel.Operators.LiSixQuarkLocalBasis]
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
