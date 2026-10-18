import Physics.StandardModel.Operators.FlavoredCyclicControls
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
    ``GUT.FlavoredCyclicCoordinates.llhhEquiv,
    ``GUT.FlavoredCyclicCoordinates.llhh_finrank,
    ``GUT.FlavoredCyclicCoordinates.llhh_allowed,
    ``GUT.FlavoredCyclicCoordinates.duqlEquiv,
    ``GUT.FlavoredCyclicCoordinates.duql_finrank,
    ``GUT.FlavoredCyclicCoordinates.duql_allowed,
    ``GUT.FlavoredCyclicCoordinates.qqueEquiv,
    ``GUT.FlavoredCyclicCoordinates.qque_finrank,
    ``GUT.FlavoredCyclicCoordinates.qque_allowed,
    ``GUT.FlavoredCyclicCoordinates.duueEquiv,
    ``GUT.FlavoredCyclicCoordinates.duue_finrank,
    ``GUT.FlavoredCyclicCoordinates.duue_allowed,
    ``GUT.FlavoredCyclicCoordinates.duql_forbidden,
    ``GUT.FlavoredCyclicCoordinates.qque_forbidden,
    ``GUT.FlavoredCyclicCoordinates.duue_forbidden,
    ``GUT.FlavoredCyclicCoordinates.llhh_forbidden,
    ``GUT.QqqlDiagonalCoordinates.residual_iff_supported,
    ``GUT.QqqlDiagonalCoordinates.equiv,
    ``GUT.QqqlDiagonalCoordinates.finrank,
    ``GUT.QqqlDiagonalCoordinates.allowed_iff,
    ``GUT.QqqlDiagonalCoordinates.diagonalEquiv,
    ``GUT.QqqlDiagonalCoordinates.diagonal_allowed_iff,
    ``GUT.QqqlDiagonalCoordinates.diagonal_forbidden_iff,
    ``GUT.FlavoredCyclicSelection.opposite_charge,
    ``GUT.FlavoredCyclicSelection.opposite_slot,
    ``GUT.FlavoredCyclicSelection.equiv,
    ``GUT.FlavoredCyclicSelection.reconstruct_extract,
    ``GUT.FlavoredCyclicSelection.extract_reconstruct,
    ``GUT.FlavoredCyclicSelection.finrank_total,
    ``GUT.FlavoredCyclicSelection.forbidden_total_iff,
    ``GUT.FlavoredCyclicSelection.allowed_total_iff,
    ``GUT.FlavoredCyclicSelection.simultaneous_iff,
    ``GUT.FlavoredCyclicControls.trivial_three_generation,
    ``GUT.FlavoredCyclicControls.empty_total,
    ``GUT.FlavoredCyclicControls.empty_weinberg,
    ``GUT.FlavoredCyclicControls.unequal_species_total,
    ``GUT.FlavoredCyclicControls.nonuniform_qqql,
    ``GUT.FlavoredCyclicControls.nonuniform_ordered_count,
    ``GUT.FlavoredCyclicControls.singleton_quarkParity_forbidden,
    ``GUT.FlavoredCyclicControls.singleton_quarkParity_weinberg,
    ``GUT.FlavoredCyclicControls.singleton_forbidden_iff,
    ``GUT.FlavoredCyclicControls.singleton_weinberg_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Flavored selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Flavored cyclic selection: {ds.length} strict transitive checks passed"
