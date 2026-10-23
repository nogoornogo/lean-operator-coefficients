import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorResidualHom
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTypedFlavor
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorOneGeneration
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorOneGeneration
import Lean.Util.CollectAxioms

open Math

run_cmd do
  let declarations := [
    ``Physics.SixQuarkSpeciesQuotient.generators_species_sign,
    ``Physics.SixQuarkFlavorCoordinates.coordinateLinear,
    ``Physics.SixQuarkFlavorCoordinates.fixedFlavorMap,
    ``Physics.SixQuarkFlavorCoordinates.coordinates_formula,
    ``Physics.SixQuarkFlavorCoordinates.eq_of_coordinates,
    ``Physics.SixQuarkFlavorCoordinates.residual_invariance_iff,
    ``Physics.SixQuarkFlavorCoordinates.assemble_apply,
    ``Physics.SixQuarkFlavorCoordinates.assemble_invariant,
    ``Physics.SixQuarkFlavorCoordinates.coordinates_assemble,
    ``Physics.SixQuarkFlavorCoordinates.assemble_coordinates,
    ``Physics.SixQuarkFlavorCoordinates.swaps_iff_species,
    ``Physics.SixQuarkFlavorCoordinates.statistics_iff,
    ``Physics.SixQuarkFlavorResidualHom.homCoordinates_residualHom,
    ``Physics.SixQuarkFlavorResidualHom.assembleHom_residualInvariant,
    ``Physics.SixQuarkFlavorResidualHom.assembleHom_residualHom,
    ``Physics.SixQuarkFlavorResidualHom.residualHom_assembleHom,
    ``Physics.SixQuarkFlavorResidualHom.statisticsEquiv,
    ``Physics.SixQuarkFlavorResidualHom.statisticsLinearEquiv,
    ``Physics.SixQuarkFlavorResidualHom.exists_nonzero_statistics_iff,
    ``Physics.SixQuarkFlavorCoordinates.typed_statistics_iff,
    ``Physics.SixQuarkTypedFlavor.speciesExchange,
    ``Physics.SixQuarkTypedFlavor.swapCoefficient_apply,
    ``Physics.SixQuarkTypedFlavor.typed_swap_full,
    ``Physics.SixQuarkTypedFlavor.homLinearEquiv,
    ``Physics.SixQuarkTypedFlavor.exists_nonzero_iff,
    ``Physics.SixQuarkFlavorOneGeneration.scalarFlavorEquiv,
    ``Physics.SixQuarkFlavorOneGeneration.twoProbeEquiv,
    ``Physics.SixQuarkFlavorOneGeneration.homTwoProbeEquiv,
    ``Physics.SixQuarkFlavorOneGeneration.finrank_scalarFlavor,
    ``Physics.SixQuarkFlavorOneGeneration.finrank_scalarHom,
    ``Physics.DeltaBTwoFlavorBridge.reorder,
    ``Physics.DeltaBTwoFlavorBridge.reorder_up_action,
    ``Physics.DeltaBTwoFlavorBridge.reorder_down_action,
    ``Physics.DeltaBTwoFlavorBridge.phase_product,
    ``Physics.DeltaBTwoFlavorBridge.physical_invariance_iff,
    ``Math.SixSlotSpeciesRestriction.evaluation_apply,
    ``Math.SixSlotSpeciesRestriction.ofEvaluation,
    ``Math.SixSlotSpeciesRestriction.ofEvaluation_degree,
    ``Math.SixSlotSpeciesRestriction.alternatization_slots,
    ``Math.SixSlotSpeciesRestriction.sector_ext,
    ``Physics.DeltaBTwoFlavorBridge.embedSlot_action,
    ``Physics.DeltaBTwoFlavorBridge.restrictSector_invariant,
    ``Physics.DeltaBTwoFlavorBridge.restrictSector_typedAlternating,
    ``Physics.DeltaBTwoFlavorBridge.restriction_slots_eq,
    ``Physics.DeltaBTwoFlavorBridge.restrictSector_injective,
    ``Physics.DeltaBTwoFlavorBridge.sectorHom,
    ``Physics.DeltaBTwoFlavorBridge.projected_species,
    ``Physics.DeltaBTwoFlavorBridge.normalizedAlternating_invariant,
    ``Physics.DeltaBTwoFlavorBridge.normalizedAlternating_scaling,
    ``Physics.DeltaBTwoFlavorBridge.descended_degree,
    ``Physics.DeltaBTwoFlavorBridge.restrict_lift,
    ``Physics.DeltaBTwoFlavorBridge.lift_restrictedCoefficient,
    ``Physics.DeltaBTwoFlavorBridge.sectorHomEquiv,
    ``Physics.DeltaBTwoFlavorBridge.sectorHom_surjective,
    ``Physics.DeltaBTwoFlavorBridge.exists_nonzero_sector_iff,
    ``Physics.DeltaBTwoFlavorBridge.onFieldsHomEquiv,
    ``Physics.DeltaBTwoFlavorBridge.exists_nonzero_onFields_iff,
    ``Physics.DeltaBTwoFlavorOneGeneration.typedScalarEquiv,
    ``Physics.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv,
    ``Physics.DeltaBTwoFlavorOneGeneration.inverse_twoProbes,
    ``Physics.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv_symm_apply,
    ``Physics.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv,
    ``Physics.DeltaBTwoFlavorOneGeneration.finrank_hom,
    ``Physics.DeltaBTwoFlavorOneGeneration.finrank_physical,
    ``Physics.DeltaBTwoFlavorOneGeneration.onFieldsTwoProbeEquiv,
    ``Physics.DeltaBTwoFlavorOneGeneration.finrank_onFields,
    ``Physics.DeltaBTwoFlavorBridge.sectorHomLinear,
    ``Physics.DeltaBTwoFlavorBridge.sectorHom_injective,
    ``Physics.DeltaBTwoFlavorBridge.sectorHom_ne_zero_iff,
    ``Physics.DeltaBTwoFlavorBridge.onFieldsHomLinear,
    ``Physics.DeltaBTwoFlavorBridge.onFieldsHom_injective,
    ``Physics.DeltaBTwoFlavorBridge.onFieldsHom_ne_zero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-quark flavor Hom audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-quark flavor Hom audit: {declarations.length} strict checks passed"
