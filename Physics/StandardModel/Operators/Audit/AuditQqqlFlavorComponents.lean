import Physics.StandardModel.Operators.LiQqqlConvention
import Physics.StandardModel.Operators.QqqlFiniteFlavor
import Physics.StandardModel.Operators.LiQqqlExterior
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Strict source-layer and transitive trust audit for the component inverse. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Qqql components import model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.FourDoubletProductComponents.equiv,
    ``Math.FourDoubletProductComponents.moduleEquiv,
    ``Math.FourDoubletProductComponents.exchange01_assemble,
    ``Math.FourDoubletProductComponents.exchange12_assemble,
    ``GUT.QqqlFlavorComponents.condition_iff,
    ``GUT.QqqlFlavorComponents.mem_residualSpace_iff,
    ``GUT.QqqlFlavorComponents.residualEquiv,
    ``GUT.QqqlFlavorComponents.exteriorEquiv,
    ``GUT.QqqlFlavorComponents.inverse_left,
    ``GUT.QqqlFlavorComponents.inverse_right,
    ``GUT.QqqlFlavorComponents.component_relations,
    ``GUT.QqqlFlavorComponents.condition_iff_component_relations,
    ``Math.TripleMixedCoordinates.equiv,
    ``Math.TripleMixedCoordinates.assemble_extract,
    ``Math.TripleMixedCoordinates.extract_assemble,
    ``Math.TripleMixedCoordinates.condition_assemble,
    ``Math.TripleMixedCoordinates.finrank_eq_index_card,
    ``Math.TripleMixedCoordinates.index_card_zero,
    ``Math.TripleMixedCoordinates.index_card_one,
    ``Math.TripleMixedCoordinates.index_card_two,
    ``Math.TripleMixedCoordinates.index_card_three,
    ``GUT.QqqlFlavorComponents.mixed_reconstruction,
    ``GUT.LiQqqlConvention.fermionic_reorder,
    ``GUT.LiQqqlConvention.seed_components,
    ``GUT.LiQqqlConvention.seed_symmetric_nonzero,
    ``GUT.LiQqqlConvention.seed_alternating_nonzero,
    ``GUT.LiQqqlConvention.seed_mixed_nonzero,
    ``Math.TripleSymmetricCoordinates.equiv,
    ``Math.TripleAlternatingCoordinates.equiv,
    ``Math.TripleFlavorCoordinates.equiv,
    ``Math.TripleFlavorCounting.triple_card,
    ``Math.TripleFlavorCounting.symmetric_card,
    ``Math.TripleFlavorCounting.pair_card,
    ``Math.TripleFlavorCounting.index_card,
    ``GUT.QqqlFlavorComponents.flavorCoordinates_injective,
    ``GUT.QqqlFiniteFlavor.extract_reconstruct,
    ``GUT.QqqlFiniteFlavor.reconstruct_extract,
    ``GUT.QqqlFiniteFlavor.equiv,
    ``GUT.QqqlFiniteFlavor.exteriorEquiv,
    ``GUT.QqqlFiniteFlavor.flavorEquiv,
    ``GUT.QqqlFiniteFlavor.flavorBasis_independent,
    ``GUT.QqqlFiniteFlavor.flavorBasis_spans,
    ``GUT.QqqlFiniteFlavor.flavor_finrank_binomial,
    ``GUT.QqqlFiniteFlavor.three_generation_finrank,
    ``GUT.QqqlFiniteFlavor.onFieldsEquiv,
    ``Math.FourSlotTripleAlternation.alternating_slots_orbit,
    ``GUT.LiQqqlConvention.orbit_inverse,
    ``GUT.LiQqqlConvention.source_orbit,
    ``GUT.LiQqqlExterior.restriction_candidate,
    ``GUT.LiQqqlExterior.candidate_eq,
    ``GUT.LiQqqlExterior.every_sector_is_candidate,
    ``GUT.LiQqqlExterior.candidate_injective]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Qqql components: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Qqql components: {declarations.length} strict axiom checks passed"
