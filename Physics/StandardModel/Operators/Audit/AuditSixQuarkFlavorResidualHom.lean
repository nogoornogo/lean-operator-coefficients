import Physics.StandardModel.Operators.SixQuarkFlavorResidualHom
import Physics.StandardModel.Operators.SixQuarkTypedFlavor
import Physics.StandardModel.Operators.SixQuarkFlavorOneGeneration
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.DeltaBTwoFlavorOneGeneration
import Lean.Util.CollectAxioms

open Math

run_cmd do
  let declarations := [
    ``GUT.SixQuarkSpeciesQuotient.generators_species_sign,
    ``GUT.SixQuarkFlavorCoordinates.coordinateLinear,
    ``GUT.SixQuarkFlavorCoordinates.fixedFlavorMap,
    ``GUT.SixQuarkFlavorCoordinates.coordinates_formula,
    ``GUT.SixQuarkFlavorCoordinates.eq_of_coordinates,
    ``GUT.SixQuarkFlavorCoordinates.residual_invariance_iff,
    ``GUT.SixQuarkFlavorCoordinates.assemble_apply,
    ``GUT.SixQuarkFlavorCoordinates.assemble_invariant,
    ``GUT.SixQuarkFlavorCoordinates.coordinates_assemble,
    ``GUT.SixQuarkFlavorCoordinates.assemble_coordinates,
    ``GUT.SixQuarkFlavorCoordinates.swaps_iff_species,
    ``GUT.SixQuarkFlavorCoordinates.statistics_iff,
    ``GUT.SixQuarkFlavorResidualHom.homCoordinates_residualHom,
    ``GUT.SixQuarkFlavorResidualHom.assembleHom_residualInvariant,
    ``GUT.SixQuarkFlavorResidualHom.assembleHom_residualHom,
    ``GUT.SixQuarkFlavorResidualHom.residualHom_assembleHom,
    ``GUT.SixQuarkFlavorResidualHom.statisticsEquiv,
    ``GUT.SixQuarkFlavorResidualHom.statisticsLinearEquiv,
    ``GUT.SixQuarkFlavorResidualHom.exists_nonzero_statistics_iff,
    ``GUT.SixQuarkFlavorCoordinates.typed_statistics_iff,
    ``GUT.SixQuarkTypedFlavor.speciesExchange,
    ``GUT.SixQuarkTypedFlavor.swapCoefficient_apply,
    ``GUT.SixQuarkTypedFlavor.typed_swap_full,
    ``GUT.SixQuarkTypedFlavor.homLinearEquiv,
    ``GUT.SixQuarkTypedFlavor.exists_nonzero_iff,
    ``GUT.SixQuarkFlavorOneGeneration.scalarFlavorEquiv,
    ``GUT.SixQuarkFlavorOneGeneration.twoProbeEquiv,
    ``GUT.SixQuarkFlavorOneGeneration.homTwoProbeEquiv,
    ``GUT.SixQuarkFlavorOneGeneration.finrank_scalarFlavor,
    ``GUT.SixQuarkFlavorOneGeneration.finrank_scalarHom,
    ``GUT.DeltaBTwoFlavorBridge.reorder,
    ``GUT.DeltaBTwoFlavorBridge.reorder_up_action,
    ``GUT.DeltaBTwoFlavorBridge.reorder_down_action,
    ``GUT.DeltaBTwoFlavorBridge.phase_product,
    ``GUT.DeltaBTwoFlavorBridge.physical_invariance_iff,
    ``Math.SixSlotSpeciesRestriction.evaluation_apply,
    ``Math.SixSlotSpeciesRestriction.ofEvaluation,
    ``Math.SixSlotSpeciesRestriction.ofEvaluation_degree,
    ``Math.SixSlotSpeciesRestriction.alternatization_slots,
    ``Math.SixSlotSpeciesRestriction.sector_ext,
    ``GUT.DeltaBTwoFlavorBridge.embedSlot_action,
    ``GUT.DeltaBTwoFlavorBridge.restrictSector_invariant,
    ``GUT.DeltaBTwoFlavorBridge.restrictSector_typedAlternating,
    ``GUT.DeltaBTwoFlavorBridge.restriction_slots_eq,
    ``GUT.DeltaBTwoFlavorBridge.restrictSector_injective,
    ``GUT.DeltaBTwoFlavorBridge.sectorHom,
    ``GUT.DeltaBTwoFlavorBridge.projected_species,
    ``GUT.DeltaBTwoFlavorBridge.normalizedAlternating_invariant,
    ``GUT.DeltaBTwoFlavorBridge.normalizedAlternating_scaling,
    ``GUT.DeltaBTwoFlavorBridge.descended_degree,
    ``GUT.DeltaBTwoFlavorBridge.restrict_lift,
    ``GUT.DeltaBTwoFlavorBridge.lift_restrictedCoefficient,
    ``GUT.DeltaBTwoFlavorBridge.sectorHomEquiv,
    ``GUT.DeltaBTwoFlavorBridge.sectorHom_surjective,
    ``GUT.DeltaBTwoFlavorBridge.exists_nonzero_sector_iff,
    ``GUT.DeltaBTwoFlavorBridge.onFieldsHomEquiv,
    ``GUT.DeltaBTwoFlavorBridge.exists_nonzero_onFields_iff,
    ``GUT.DeltaBTwoFlavorOneGeneration.typedScalarEquiv,
    ``GUT.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv,
    ``GUT.DeltaBTwoFlavorOneGeneration.inverse_twoProbes,
    ``GUT.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv_symm_apply,
    ``GUT.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv,
    ``GUT.DeltaBTwoFlavorOneGeneration.finrank_hom,
    ``GUT.DeltaBTwoFlavorOneGeneration.finrank_physical,
    ``GUT.DeltaBTwoFlavorOneGeneration.onFieldsTwoProbeEquiv,
    ``GUT.DeltaBTwoFlavorOneGeneration.finrank_onFields,
    ``GUT.DeltaBTwoFlavorBridge.sectorHomLinear,
    ``GUT.DeltaBTwoFlavorBridge.sectorHom_injective,
    ``GUT.DeltaBTwoFlavorBridge.sectorHom_ne_zero_iff,
    ``GUT.DeltaBTwoFlavorBridge.onFieldsHomLinear,
    ``GUT.DeltaBTwoFlavorBridge.onFieldsHom_injective,
    ``GUT.DeltaBTwoFlavorBridge.onFieldsHom_ne_zero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-quark flavor Hom audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-quark flavor Hom audit: {declarations.length} strict checks passed"
