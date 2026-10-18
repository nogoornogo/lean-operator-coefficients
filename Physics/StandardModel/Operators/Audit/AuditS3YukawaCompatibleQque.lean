import Physics.StandardModel.Operators.S3YukawaCompatibleQque
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.S3YukawaCompatibleQque.quarkFlavor,
    ``GUT.S3YukawaCompatibleQque.leptonFlavor,
    ``GUT.S3YukawaCompatibleQque.higgsFlavor,
    ``GUT.S3YukawaCompatibleQque.higgsFlavor_apply,
    ``GUT.S3YukawaCompatibleQque.quarkFlavorMap,
    ``GUT.S3YukawaCompatibleQque.leptonFlavorMap,
    ``GUT.S3YukawaCompatibleQque.quarkFlavorMap_bijective,
    ``GUT.S3YukawaCompatibleQque.leptonFlavorMap_bijective,
    ``GUT.S3YukawaCompatibleQque.Species,
    ``GUT.S3YukawaCompatibleQque.flavor,
    ``GUT.S3YukawaCompatibleQque.flavor_map_gates,
    ``GUT.S3YukawaCompatibleQque.preserves_sm,
    ``GUT.S3YukawaCompatibleQque.quark_actions_noncommute,
    ``GUT.S3YukawaCompatibleQque.pairCoordinate,
    ``GUT.S3YukawaCompatibleQque.lastCoordinate,
    ``GUT.S3YukawaCompatibleQque.term,
    ``GUT.S3YukawaCompatibleQque.coefficient,
    ``GUT.S3YukawaCompatibleQque.coefficient_apply,
    ``GUT.S3YukawaCompatibleQque.coefficient_invariant,
    ``GUT.S3YukawaCompatibleQque.invariantCoefficient,
    ``GUT.S3YukawaCompatibleQque.symmetricResidual,
    ``GUT.S3YukawaCompatibleQque.witness,
    ``GUT.S3YukawaCompatibleQque.residual_nonzero,
    ``GUT.S3YukawaCompatibleQque.allowed,
    ``GUT.S3YukawaCompatibleQque.allowed_dictionary]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "S3 Yukawa-compatible qque: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"S3 Yukawa-compatible qque: {ds.length} strict transitive checks passed"
