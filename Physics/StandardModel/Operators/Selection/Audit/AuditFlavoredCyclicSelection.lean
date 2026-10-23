import Physics.StandardModel.Operators.Selection.FlavoredCyclicControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Flavored selection imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.CyclicWeightCoordinates.diagonal,
    ``Math.CyclicWeightCoordinates.diagonal_basis,
    ``Math.CyclicWeightCoordinates.supportedEquiv,
    ``Math.CyclicWeightCoordinates.invariant_iff,
    ``Math.CyclicWeightCoordinates.invariantEquiv,
    ``Math.CyclicWeightCoordinates.finrank,
    ``Math.CyclicWeightCoordinates.allowed_iff,
    ``Math.CyclicWeightCoordinates.tensor_weights,
    ``Math.CyclicWeightCoordinates.symmetric_weights,
    ``Math.SymmetricTensorFunctional.equiv,
    ``Math.TripleFlavorWeights.symmetric_assemble,
    ``Math.TripleFlavorWeights.alternating_assemble,
    ``Math.TripleFlavorWeights.mixed_assemble,
    ``Physics.FlavoredCyclicCoordinates.llhhEquiv,
    ``Physics.FlavoredCyclicCoordinates.llhh_finrank,
    ``Physics.FlavoredCyclicCoordinates.llhh_allowed,
    ``Physics.FlavoredCyclicCoordinates.duqlEquiv,
    ``Physics.FlavoredCyclicCoordinates.duql_finrank,
    ``Physics.FlavoredCyclicCoordinates.duql_allowed,
    ``Physics.FlavoredCyclicCoordinates.qqueEquiv,
    ``Physics.FlavoredCyclicCoordinates.qque_finrank,
    ``Physics.FlavoredCyclicCoordinates.qque_allowed,
    ``Physics.FlavoredCyclicCoordinates.duueEquiv,
    ``Physics.FlavoredCyclicCoordinates.duue_finrank,
    ``Physics.FlavoredCyclicCoordinates.duue_allowed,
    ``Physics.FlavoredCyclicCoordinates.duql_forbidden,
    ``Physics.FlavoredCyclicCoordinates.qque_forbidden,
    ``Physics.FlavoredCyclicCoordinates.duue_forbidden,
    ``Physics.FlavoredCyclicCoordinates.llhh_forbidden,
    ``Physics.QqqlDiagonalCoordinates.residual_iff_supported,
    ``Physics.QqqlDiagonalCoordinates.equiv,
    ``Physics.QqqlDiagonalCoordinates.finrank,
    ``Physics.QqqlDiagonalCoordinates.allowed_iff,
    ``Physics.QqqlDiagonalCoordinates.diagonalEquiv,
    ``Physics.QqqlDiagonalCoordinates.diagonal_allowed_iff,
    ``Physics.QqqlDiagonalCoordinates.diagonal_forbidden_iff,
    ``Physics.FlavoredCyclicSelection.opposite_charge,
    ``Physics.FlavoredCyclicSelection.opposite_slot,
    ``Physics.FlavoredCyclicSelection.equiv,
    ``Physics.FlavoredCyclicSelection.reconstruct_extract,
    ``Physics.FlavoredCyclicSelection.extract_reconstruct,
    ``Physics.FlavoredCyclicSelection.finrank_total,
    ``Physics.FlavoredCyclicSelection.forbidden_total_iff,
    ``Physics.FlavoredCyclicSelection.allowed_total_iff,
    ``Physics.FlavoredCyclicSelection.simultaneous_iff,
    ``Physics.FlavoredCyclicControls.trivial_three_generation,
    ``Physics.FlavoredCyclicControls.empty_total,
    ``Physics.FlavoredCyclicControls.empty_weinberg,
    ``Physics.FlavoredCyclicControls.unequal_species_total,
    ``Physics.FlavoredCyclicControls.nonuniform_qqql,
    ``Physics.FlavoredCyclicControls.nonuniform_ordered_count,
    ``Physics.FlavoredCyclicControls.singleton_quarkParity_forbidden,
    ``Physics.FlavoredCyclicControls.singleton_quarkParity_weinberg,
    ``Physics.FlavoredCyclicControls.singleton_forbidden_iff,
    ``Physics.FlavoredCyclicControls.singleton_weinberg_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Flavored selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Flavored cyclic selection: {ds.length} strict transitive checks passed"
