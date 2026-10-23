import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSourceTransport
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSeedDirections
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! The actual-source derivation is independently usable without the old
finite-data, selected-orbit or basis certificates. -/
run_cmd do
  let env ← Lean.getEnv
  let bannedModules := [
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFiniteData,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitData,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkCertificate,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkConvention,
    `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalBasis]
  for mod in env.header.moduleNames do
    if bannedModules.contains mod || (`GUT).isPrefixOf mod then
      throwError "Source derivation imports excluded module {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.LiSixQuarkRawSource.rawCoefficient_reconstruct,
    ``Physics.LiSixQuarkSemanticSeeds.coordinates_seedCoefficient,
    ``Physics.LiSixQuarkSourceTransport.candidate_eq_semantic,
    ``Physics.LiSixQuarkSourceTransport.candidate_coordinates,
    ``Physics.LiSixQuarkSeedRecipe.rational_cast,
    ``Physics.LiSixQuarkReducedAction.extraction_action,
    ``Physics.LiSixQuarkYoungImages.image0,
    ``Physics.LiSixQuarkYoungImages.image2,
    ``Physics.LiSixQuarkYoungImages.image4,
    ``Physics.LiSixQuarkYoungImages.image6,
    ``Physics.LiSixQuarkYoungImages.image7,
    ``Physics.LiSixQuarkYoungImages.image9,
    ``Physics.LiSixQuarkYoungImages.image10,
    ``Physics.LiSixQuarkReducedSeeds.extraction_projected,
    ``Physics.LiSixQuarkSeedDirections.reducedSeed_direction]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Source derivation: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li actual-source derivation: {ds.length} strict checks; old finite-data imports absent"
