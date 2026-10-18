import Physics.StandardModel.Operators.LiSixQuarkSourceTransport
import Physics.StandardModel.Operators.LiSixQuarkSeedDirections
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! The actual-source derivation is independently usable without the old
finite-data, selected-orbit or basis certificates. -/
run_cmd do
  let env ← Lean.getEnv
  let bannedModules := [
    `Physics.StandardModel.Operators.LiSixQuarkFiniteData,
    `Physics.StandardModel.Operators.LiSixQuarkOrbitData,
    `Physics.StandardModel.Operators.LiSixQuarkCertificate,
    `Physics.StandardModel.Operators.LiSixQuarkConvention,
    `Physics.StandardModel.Operators.LiSixQuarkLocalBasis]
  for mod in env.header.moduleNames do
    if bannedModules.contains mod || (`GUT).isPrefixOf mod then
      throwError "Source derivation imports excluded module {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiSixQuarkRawSource.rawCoefficient_reconstruct,
    ``GUT.LiSixQuarkSemanticSeeds.coordinates_seedCoefficient,
    ``GUT.LiSixQuarkSourceTransport.candidate_eq_semantic,
    ``GUT.LiSixQuarkSourceTransport.candidate_coordinates,
    ``GUT.LiSixQuarkSeedRecipe.rational_cast,
    ``GUT.LiSixQuarkReducedAction.extraction_action,
    ``GUT.LiSixQuarkYoungImages.image0,
    ``GUT.LiSixQuarkYoungImages.image2,
    ``GUT.LiSixQuarkYoungImages.image4,
    ``GUT.LiSixQuarkYoungImages.image6,
    ``GUT.LiSixQuarkYoungImages.image7,
    ``GUT.LiSixQuarkYoungImages.image9,
    ``GUT.LiSixQuarkYoungImages.image10,
    ``GUT.LiSixQuarkReducedSeeds.extraction_projected,
    ``GUT.LiSixQuarkSeedDirections.reducedSeed_direction]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Source derivation: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li actual-source derivation: {ds.length} strict checks; old finite-data imports absent"
