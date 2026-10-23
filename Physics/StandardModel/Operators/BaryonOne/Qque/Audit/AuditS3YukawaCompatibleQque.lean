import Physics.StandardModel.Operators.BaryonOne.Qque.S3YukawaCompatibleQque
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``Physics.S3YukawaCompatibleQque.quarkFlavor,
    ``Physics.S3YukawaCompatibleQque.leptonFlavor,
    ``Physics.S3YukawaCompatibleQque.higgsFlavor,
    ``Physics.S3YukawaCompatibleQque.higgsFlavor_apply,
    ``Physics.S3YukawaCompatibleQque.quarkFlavorMap,
    ``Physics.S3YukawaCompatibleQque.leptonFlavorMap,
    ``Physics.S3YukawaCompatibleQque.quarkFlavorMap_bijective,
    ``Physics.S3YukawaCompatibleQque.leptonFlavorMap_bijective,
    ``Physics.S3YukawaCompatibleQque.Species,
    ``Physics.S3YukawaCompatibleQque.flavor,
    ``Physics.S3YukawaCompatibleQque.flavor_map_gates,
    ``Physics.S3YukawaCompatibleQque.preserves_sm,
    ``Physics.S3YukawaCompatibleQque.quark_actions_noncommute,
    ``Physics.S3YukawaCompatibleQque.pairCoordinate,
    ``Physics.S3YukawaCompatibleQque.lastCoordinate,
    ``Physics.S3YukawaCompatibleQque.term,
    ``Physics.S3YukawaCompatibleQque.coefficient,
    ``Physics.S3YukawaCompatibleQque.coefficient_apply,
    ``Physics.S3YukawaCompatibleQque.coefficient_invariant,
    ``Physics.S3YukawaCompatibleQque.invariantCoefficient,
    ``Physics.S3YukawaCompatibleQque.symmetricResidual,
    ``Physics.S3YukawaCompatibleQque.witness,
    ``Physics.S3YukawaCompatibleQque.residual_nonzero,
    ``Physics.S3YukawaCompatibleQque.allowed,
    ``Physics.S3YukawaCompatibleQque.allowed_dictionary]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "S3 Yukawa-compatible qque: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"S3 Yukawa-compatible qque: {ds.length} strict transitive checks passed"
