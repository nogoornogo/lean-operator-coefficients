import Physics.StandardModel.Operators.BaryonOne.Qqql.LiQqqlConvention
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFiniteFlavor
import Physics.StandardModel.Operators.BaryonOne.Qqql.LiQqqlExterior
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
    ``Physics.QqqlFlavorComponents.condition_iff,
    ``Physics.QqqlFlavorComponents.mem_residualSpace_iff,
    ``Physics.QqqlFlavorComponents.residualEquiv,
    ``Physics.QqqlFlavorComponents.exteriorEquiv,
    ``Physics.QqqlFlavorComponents.inverse_left,
    ``Physics.QqqlFlavorComponents.inverse_right,
    ``Physics.QqqlFlavorComponents.component_relations,
    ``Physics.QqqlFlavorComponents.condition_iff_component_relations,
    ``Math.TripleMixedCoordinates.equiv,
    ``Math.TripleMixedCoordinates.assemble_extract,
    ``Math.TripleMixedCoordinates.extract_assemble,
    ``Math.TripleMixedCoordinates.condition_assemble,
    ``Math.TripleMixedCoordinates.finrank_eq_index_card,
    ``Math.TripleMixedCoordinates.index_card_zero,
    ``Math.TripleMixedCoordinates.index_card_one,
    ``Math.TripleMixedCoordinates.index_card_two,
    ``Math.TripleMixedCoordinates.index_card_three,
    ``Physics.QqqlFlavorComponents.mixed_reconstruction,
    ``Physics.LiQqqlConvention.fermionic_reorder,
    ``Physics.LiQqqlConvention.seed_components,
    ``Physics.LiQqqlConvention.seed_symmetric_nonzero,
    ``Physics.LiQqqlConvention.seed_alternating_nonzero,
    ``Physics.LiQqqlConvention.seed_mixed_nonzero,
    ``Math.TripleSymmetricCoordinates.equiv,
    ``Math.TripleAlternatingCoordinates.equiv,
    ``Math.TripleFlavorCoordinates.equiv,
    ``Math.TripleFlavorCounting.triple_card,
    ``Math.TripleFlavorCounting.symmetric_card,
    ``Math.TripleFlavorCounting.pair_card,
    ``Math.TripleFlavorCounting.index_card,
    ``Physics.QqqlFlavorComponents.flavorCoordinates_injective,
    ``Physics.QqqlFiniteFlavor.extract_reconstruct,
    ``Physics.QqqlFiniteFlavor.reconstruct_extract,
    ``Physics.QqqlFiniteFlavor.equiv,
    ``Physics.QqqlFiniteFlavor.exteriorEquiv,
    ``Physics.QqqlFiniteFlavor.flavorEquiv,
    ``Physics.QqqlFiniteFlavor.flavorBasis_independent,
    ``Physics.QqqlFiniteFlavor.flavorBasis_spans,
    ``Physics.QqqlFiniteFlavor.flavor_finrank_binomial,
    ``Physics.QqqlFiniteFlavor.three_generation_finrank,
    ``Physics.QqqlFiniteFlavor.onFieldsEquiv,
    ``Math.FourSlotTripleAlternation.alternating_slots_orbit,
    ``Physics.LiQqqlConvention.orbit_inverse,
    ``Physics.LiQqqlConvention.source_orbit,
    ``Physics.LiQqqlExterior.restriction_candidate,
    ``Physics.LiQqqlExterior.candidate_eq,
    ``Physics.LiQqqlExterior.every_sector_is_candidate,
    ``Physics.LiQqqlExterior.candidate_injective]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Qqql components: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Qqql components: {declarations.length} strict axiom checks passed"
