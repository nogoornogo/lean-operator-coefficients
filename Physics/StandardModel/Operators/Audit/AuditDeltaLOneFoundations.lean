import Physics.StandardModel.Operators.DeltaLOneSpeciesSupport
import Physics.StandardModel.Operators.DuqlOrderedCompleteness
import Physics.StandardModel.Operators.DuqlExteriorCompleteness
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Physics.StandardModel.Operators.DuueOrderedCompleteness
import Physics.StandardModel.Operators.DuueExchange
import Physics.StandardModel.Operators.DuueScalarFlavor
import Physics.StandardModel.Operators.FourWeakWeylCompleteness
import Physics.StandardModel.Operators.QqqlExchange
import Physics.StandardModel.Operators.QqqlLocalCompleteness
import Math.RepresentationTheory.FourSlotTripleRestriction
import Physics.StandardModel.Operators.QqqlExteriorCompleteness
import Physics.StandardModel.Operators.QqqlScalarFlavor
import Physics.FieldTheory.Spinor.OddWeylInvariant
import Physics.StandardModel.Operators.QquePhysicalResidualHom
import Physics.StandardModel.Operators.DeltaLOneSignedFields
import Physics.StandardModel.Operators.DeltaLOneFourFamilyDecomposition
import Physics.StandardModel.Operators.DeltaLOneConjugation
import Physics.StandardModel.Operators.DeltaLOneRegression
import Math.RepresentationTheory.FourSlotCoefficientEquiv
import Math.RepresentationTheory.DistinctSpeciesAlternation
import Lean.Util.CollectAxioms

open Math

run_cmd do
  let declarations := [
    ``GUT.DeltaLOneSpeciesSupport.admissible_iff,
    ``GUT.DeltaLOneSpeciesSupport.baryonDegree_of_admissible,
    ``GUT.DeltaLOneSpeciesSupport.no_conjugates,
    ``GUT.DuqlGaugeUniqueness.unique,
    ``GUT.DuqlOrderedCompleteness.spin_unique,
    ``GUT.DuqlOrderedCompleteness.local_normalized,
    ``GUT.DuqlOrderedCompleteness.local_unique,
    ``GUT.DuqlOrderedCompleteness.homEquiv,
    ``GUT.DuqlOrderedCompleteness.exists_nonzero_iff,
    ``Math.DistinctSpeciesAlternation.restrict_assemble,
    ``Math.DistinctSpeciesAlternation.support_ext,
    ``Math.DistinctSpeciesAlternation.equiv,
    ``Math.DistinctSpeciesAlternation.invariantEquiv,
    ``Math.DistinctSpeciesAlternation.exteriorEquiv,
    ``Math.DistinctSpeciesAlternation.exteriorHomEquiv,
    ``Math.FourTensorMultilinear.equiv,
    ``Math.FourTensorMultilinear.invariantEquiv,
    ``GUT.DuqlExteriorCompleteness.orderedEquiv,
    ``GUT.DuqlExteriorCompleteness.homEquiv,
    ``GUT.DuqlExteriorCompleteness.exists_nonzero_iff,
    ``Math.FourDoubletInvariant.value_vanish,
    ``Math.FourDoubletInvariant.relation,
    ``Math.FourDoubletInvariant.formula,
    ``Math.FourDoubletInvariant.coordinates,
    ``GUT.FourSameWeylCompleteness.restrict_invariant,
    ``GUT.FourSameWeylCompleteness.formula,
    ``GUT.FourSameWeylCompleteness.coordinates,
    ``GUT.FourSameWeylCompleteness.flavorEquiv,
    ``Math.FiniteInvariantFactor.equiv,
    ``Math.FiniteInvariantFactor.product_left_line,
    ``Math.FourSlotCoefficientEquiv.equiv,
    ``GUT.DuueGaugeUniqueness.unique,
    ``GUT.DuueGaugeUniqueness.normalized,
    ``GUT.DuueOrderedCompleteness.local_formula,
    ``GUT.DuueOrderedCompleteness.homEquiv,
    ``GUT.DuueOrderedCompleteness.assemble_apply,
    ``GUT.DuueExchange.antisymmetric_iff,
    ``GUT.DuueExchange.exteriorEquiv,
    ``GUT.DuueExchange.exists_nonzero_iff,
    ``GUT.DuueResidualCompleteness.homEquiv,
    ``GUT.DuueResidualCompleteness.exists_nonzero_iff,
    ``GUT.DuueResidualCompleteness.onFieldsEquiv,
    ``GUT.DuueScalarFlavor.exists_nonzero_iff_charge_trivial,
    ``GUT.DuueScalarFlavor.oneGenerationEquiv,
    ``GUT.DuueScalarFlavor.oneGeneration_finrank,
    ``Math.FiniteInvariantFactor.product_formula,
    ``Math.FourDoubletProductExchange.evaluate_exchange01,
    ``Math.FourDoubletProductExchange.evaluate_exchange12,
    ``Math.FourDoubletProductExchange.braid,
    ``GUT.FourWeakWeylCompleteness.coordinates,
    ``GUT.QqqlExchange.antisymmetric_iff,
    ``Math.FourSlotTripleAlternation.coefficient_slots,
    ``Math.FourSlotTripleSector.slots_ext,
    ``Math.FourSlotTripleSector.coefficient_hasDegree,
    ``Math.FourSlotTripleRestriction.equiv,
    ``GUT.QqqlLocalCompleteness.color_unique,
    ``GUT.QqqlLocalCompleteness.reconstruction,
    ``GUT.QqqlLocalCompleteness.homEquiv,
    ``GUT.QqqlGaugeRegroup.equiv,
    ``GUT.QqqlOrderedCompleteness.homEquiv,
    ``GUT.QqqlOrderedCompleteness.assemble_apply,
    ``Math.FourSlotTripleAlternation.alternates_iff_adjacent,
    ``GUT.QqqlExteriorCompleteness.orderedEquiv,
    ``GUT.QqqlExteriorCompleteness.exteriorEquiv,
    ``GUT.QqqlExteriorCompleteness.exists_nonzero_iff,
    ``Math.FourSlotTripleTransport.equiv,
    ``GUT.QqqlExteriorCompleteness.onFieldsEquiv,
    ``GUT.QqqlScalarFlavor.residualEquiv,
    ``GUT.QqqlScalarFlavor.oneGeneration_finrank,
    ``GUT.OddWeylInvariant.eq_zero,
    ``GUT.OddWeylInvariant.external_eq_zero,
    ``GUT.DeltaLOneSpeciesSupport.gauge_admissible_iff,
    ``GUT.DeltaLOneSpeciesSupport.excluded_candidates_leftSlots,
    ``GUT.QquePhysicalOrderedCompleteness.homEquiv,
    ``GUT.QquePhysicalOrderedCompleteness.assemble_apply,
    ``GUT.QquePhysicalExteriorCompleteness.exteriorEquiv,
    ``GUT.QquePhysicalExteriorCompleteness.onFieldsEquiv,
    ``GUT.QquePhysicalResidualHom.homEquiv,
    ``GUT.QquePhysicalResidualHom.legacyEquiv,
    ``GUT.QquePhysicalResidualHom.exists_nonzero_iff,
    ``Math.ExteriorWeightSupport.circle_weight_zero,
    ``Math.ExteriorWeightSupport.circle_constraint,
    ``Math.FiniteSpeciesExterior.pure_ext,
    ``Math.FiniteSpeciesExterior.orderedRestriction,
    ``GUT.DeltaLOneSignedInput.gauge_candidates,
    ``GUT.DeltaLOneSignedFields.gauge_hypercharge,
    ``GUT.DeltaLOneSignedFields.gauge_center,
    ``GUT.DeltaLOneSignedFields.gauge_candidates,
    ``GUT.OddWeylInvariant.odd_product_ne_one,
    ``GUT.DeltaLOneSignedFields.odd_restriction_vanish,
    ``GUT.DeltaLOneSignedFields.four_candidates,
    ``GUT.DeltaLOneSignedFields.vanish_outside_four,
    ``GUT.DeltaLOneSignedFields.baryonDegree_of_nonzero,
    ``GUT.DeltaLOneSignedFields.no_conjugates_of_nonzero,
    ``Math.FiniteSpeciesProjection.restrict_project,
    ``Math.FiniteSpeciesProjection.partitionEquiv,
    ``GUT.DeltaLOneFourFamilyDecomposition.sector_eq_partition,
    ``GUT.DeltaLOneFourFamilyDecomposition.equiv,
    ``GUT.DeltaLOneFourFamilyDecomposition.nonzero_iff,
    ``Math.FiniteSpeciesExterior.permutation_of_counts,
    ``Math.FiniteSpeciesProjection.pattern_ext,
    ``GUT.DeltaLOneFourFamilyDecomposition.orbit,
    ``GUT.DeltaLOneFourFamilyDecomposition.family_ext,
    ``GUT.DeltaLOneFourFamilyDecomposition.canonical_ext,
    ``Math.ExteriorConjugation.equiv,
    ``GUT.DeltaLOneConjugation.equiv,
    ``GUT.DeltaLOneConjugation.nonzero_iff,
    ``Math.SpeciesPatternAssembly.alternating_pure,
    ``Math.SpeciesPatternAssembly.alternating_vanish,
    ``Math.SpeciesPatternAssembly.restrict_assemble,
    ``Math.SpeciesPatternAssembly.equiv,
    ``GUT.DeltaLOneFamilyCompleteness.duqlEquiv,
    ``GUT.DeltaLOneFamilyCompleteness.qqueEquiv,
    ``GUT.DeltaLOneFamilyCompleteness.qqqlEquiv,
    ``GUT.DeltaLOneFamilyCompleteness.duueEquiv,
    ``GUT.DeltaLOneFamilyCompleteness.stabilizer_card,
    ``GUT.DeltaLOneCoefficientCompleteness.equiv,
    ``GUT.DeltaLOneCoefficientCompleteness.reconstruct_extract,
    ``GUT.DeltaLOneCoefficientCompleteness.extract_reconstruct,
    ``GUT.DeltaLOneCoefficientCompleteness.extract_injective,
    ``GUT.DeltaLOneCoefficientCompleteness.reconstruct_surjective,
    ``GUT.DeltaLOneCoefficientCompleteness.nonzero_iff,
    ``GUT.DeltaLOneCoefficientCompleteness.negativeEquiv,
    ``GUT.DeltaLOneInputTransport.equiv,
    ``GUT.DeltaLOneInputTransport.onFieldsEquiv,
    ``GUT.DeltaLOneRegression.oneGenerationEquiv,
    ``GUT.DeltaLOneRegression.oneGeneration_finrank,
    ``GUT.DeltaLOneRegression.zero_quark_factors,
    ``GUT.DeltaLOneRegression.zero_quark_up,
    ``GUT.DeltaLOneRegression.scalarHom_vanish,
    ``GUT.DeltaLOneRegression.scalar_charge_vanish]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta L one foundations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta L one foundations: {declarations.length} strict transitive axiom checks passed"
