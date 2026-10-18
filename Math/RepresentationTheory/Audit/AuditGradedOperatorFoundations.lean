import Math.RepresentationTheory.MixedPatternAssembly
import Math.RepresentationTheory.TypedMixedTensorHom
import Math.RepresentationTheory.MixedContentGrading
import Math.RepresentationTheory.MixedCoinvariantCompleteness
import Math.RepresentationTheory.LocalRelationHom
import Math.RepresentationTheory.LocalRelationTensorHom
import Math.RepresentationTheory.TypedMixedExchangeQuotient
import Math.RepresentationTheory.TypedMixedLocalHom
import Math.RepresentationTheory.GradedMixedCompleteness
import Math.RepresentationTheory.MixedCompletenessExamples
import Math.RepresentationTheory.MixedContentBounds
import Math.RepresentationTheory.MixedTensorSeparation
import Math.RepresentationTheory.IndexedTensorSeparation
import Math.RepresentationTheory.PositiveContentGrading
import Math.RepresentationTheory.DirectSumFunctionalProduct

/-! Strict audits of typed assembly, canonical separation and graded foundations. -/
open Lean in
run_cmd do
  let ds := [
    ``Math.MixedPatternAssembly.restriction_assemble,
    ``Math.MixedPatternAssembly.restriction_assemble_eq,
    ``Math.MixedPatternAssembly.restriction_invariant,
    ``Math.MixedPatternAssembly.restriction_fermion,
    ``Math.MixedPatternAssembly.restriction_boson,
    ``Math.MixedPatternAssembly.assemble_mem,
    ``Math.MixedPatternAssembly.family_ext,
    ``Math.MixedPatternAssembly.equiv,
    ``Math.TypedMixedTensorHom.orderedEquiv,
    ``Math.TypedMixedTensorHom.pure_ext,
    ``Math.TypedMixedTensorHom.lift_apply,
    ``Math.TypedMixedTensorHom.equiv,
    ``Math.MixedContentOrbits.support_iff,
    ``Math.MixedContentOrbits.disjoint,
    ``Math.MixedContentOrbits.covers,
    ``Math.MixedContentOrbits.equiv,
    ``Math.MixedContentOrbits.selectedEquiv,
    ``Math.MixedContentGrading.stable,
    ``Math.MixedContentGrading.equiv,
    ``Math.MixedCoinvariantCompleteness.commutes,
    ``Math.MixedCoinvariantCompleteness.equiv,
    ``Math.MixedCoinvariantCompleteness.extract_mk,
    ``Math.MixedCoinvariantCompleteness.forbidden_iff,
    ``Math.MixedCoinvariantCompleteness.nonzero_iff,
    ``Math.MixedCoinvariantCompleteness.allEquiv,
    ``Math.MixedCoinvariantCompleteness.all_forbidden_iff,
    ``Math.MixedCoinvariantCompleteness.all_nonzero_iff,
    ``Math.LocalRelationHom.image_stable,
    ``Math.LocalRelationHom.equiv,
    ``Math.LocalRelationHom.equiv_mk,
    ``Math.LocalRelationHom.combinedEquiv,
    ``Math.LocalRelationHom.alongEquiv,
    ``Math.LocalRelationTensorHom.relations_stable,
    ``Math.LocalRelationTensorHom.equiv,
    ``Math.TypedMixedExchangeQuotient.stable,
    ``Math.TypedMixedExchangeQuotient.vanish_iff,
    ``Math.TypedMixedExchangeQuotient.equiv,
    ``Math.TypedMixedExchangeQuotient.equiv_mk,
    ``Math.TypedMixedLocalHom.commutes,
    ``Math.TypedMixedLocalHom.combined_eq,
    ``Math.TypedMixedLocalHom.equiv,
    ``Math.TypedMixedLocalHom.familyEquiv,
    ``Math.TypedMixedSeparatedHom.commutesF,
    ``Math.TypedMixedSeparatedHom.commutesB,
    ``Math.TypedMixedSeparatedHom.exchange_stable,
    ``Math.TypedMixedSeparatedHom.separateInputEquiv,
    ``Math.TypedMixedSeparatedHom.equiv,
    ``Math.TypedMixedSeparatedHom.familyEquiv,
    ``Math.GradedMixedCompleteness.equiv,
    ``Math.GradedMixedCompleteness.selectedEquiv,
    ``Math.GradedMixedCompleteness.selected_forbidden_iff,
    ``Math.GradedMixedCompleteness.selected_nonzero_iff,
    ``Math.ProductZeroCriteria.forbidden_iff,
    ``Math.ProductZeroCriteria.nonzero_iff,
    ``Math.GradedMixedCompleteness.allEquiv,
    ``Math.GradedMixedCompleteness.all_forbidden_iff,
    ``Math.GradedMixedCompleteness.all_nonzero_iff,
    ``Math.GradedMixedCompleteness.bounded_stable,
    ``Math.GradedMixedCompleteness.all_bounds_forbidden_iff,
    ``Math.MixedCompletenessExamples.boson_exchange,
    ``Math.MixedCompletenessExamples.fermion_exchange,
    ``Math.MixedCompletenessExamples.two_boson_exchange,
    ``Math.MixedCompletenessExamples.mixed_fermion_sign,
    ``Math.MixedCompletenessExamples.mixed_repeated_fermion_zero,
    ``Math.MixedCompletenessExamples.two_boson_reconstruct,
    ``Math.MixedCompletenessExamples.two_boson_equivalence,
    ``Math.MixedCompletenessExamples.mixed_reconstruct,
    ``Math.MixedCompletenessExamples.mixed_equivalence,
    ``Math.MixedContentBounds.slots_le,
    ``Math.MixedContentBounds.bounded_finite,
    ``Math.MixedTensorSeparation.equiv_pure,
    ``Math.MixedTensorSeparation.representationEquiv,
    ``Math.IndexedTensorSeparation.equiv_pure,
    ``Math.IndexedTensorSeparation.ext,
    ``Math.IndexedTensorSeparation.equiv_unique,
    ``Math.IndexedTensorSeparation.representationEquiv,
    ``Math.PositiveContentGrading.component_le_degree,
    ``Math.PositiveContentGrading.bounded_finite,
    ``Math.PositiveContentGrading.charged_bounded_finite,
    ``Math.PositiveContentGrading.all_bounds_iff,
    ``Math.DirectSumFunctionalProduct.equiv,
    ``Math.DirectSumFunctionalProduct.zero_iff,
    ``Math.DirectSumFunctionalProduct.forbidden_iff,
    ``Math.DirectSumFunctionalProduct.nonzero_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded operator foundation {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded operator foundations: {ds.length} strict transitive checks passed"
