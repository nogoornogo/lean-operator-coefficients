import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSpeciesSupport
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlOrderedCompleteness
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlExteriorCompleteness
import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueOrderedCompleteness
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueExchange
import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuueScalarFlavor
import Physics.StandardModel.Operators.BaryonOne.Inputs.FourWeakWeylCompleteness
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExchange
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlLocalCompleteness
import Math.RepresentationTheory.Tensors.FourSlotTripleRestriction
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExteriorCompleteness
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlScalarFlavor
import Physics.FieldTheory.Spinor.Tensors.OddWeylInvariant
import Physics.StandardModel.Operators.BaryonOne.Qque.QquePhysicalResidualHom
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedFields
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneFourFamilyDecomposition
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneConjugation
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneRegression
import Math.RepresentationTheory.Coefficients.FourSlotCoefficientEquiv
import Math.RepresentationTheory.Exterior.DistinctSpeciesAlternation
import Lean.Util.CollectAxioms

open Math

run_cmd do
  let declarations := [
    ``Physics.DeltaLOneSpeciesSupport.admissible_iff,
    ``Physics.DeltaLOneSpeciesSupport.baryonDegree_of_admissible,
    ``Physics.DeltaLOneSpeciesSupport.no_conjugates,
    ``Physics.DuqlGaugeUniqueness.unique,
    ``Physics.DuqlOrderedCompleteness.spin_unique,
    ``Physics.DuqlOrderedCompleteness.local_normalized,
    ``Physics.DuqlOrderedCompleteness.local_unique,
    ``Physics.DuqlOrderedCompleteness.homEquiv,
    ``Physics.DuqlOrderedCompleteness.exists_nonzero_iff,
    ``Math.DistinctSpeciesAlternation.restrict_assemble,
    ``Math.DistinctSpeciesAlternation.support_ext,
    ``Math.DistinctSpeciesAlternation.equiv,
    ``Math.DistinctSpeciesAlternation.invariantEquiv,
    ``Math.DistinctSpeciesAlternation.exteriorEquiv,
    ``Math.DistinctSpeciesAlternation.exteriorHomEquiv,
    ``Math.FourTensorMultilinear.equiv,
    ``Math.FourTensorMultilinear.invariantEquiv,
    ``Physics.DuqlExteriorCompleteness.orderedEquiv,
    ``Physics.DuqlExteriorCompleteness.homEquiv,
    ``Physics.DuqlExteriorCompleteness.exists_nonzero_iff,
    ``Math.FourDoubletInvariant.value_vanish,
    ``Math.FourDoubletInvariant.relation,
    ``Math.FourDoubletInvariant.formula,
    ``Math.FourDoubletInvariant.coordinates,
    ``Physics.FourSameWeylCompleteness.restrict_invariant,
    ``Physics.FourSameWeylCompleteness.formula,
    ``Physics.FourSameWeylCompleteness.coordinates,
    ``Physics.FourSameWeylCompleteness.flavorEquiv,
    ``Math.FiniteInvariantFactor.equiv,
    ``Math.FiniteInvariantFactor.product_left_line,
    ``Math.FourSlotCoefficientEquiv.equiv,
    ``Physics.DuueGaugeUniqueness.unique,
    ``Physics.DuueGaugeUniqueness.normalized,
    ``Physics.DuueOrderedCompleteness.local_formula,
    ``Physics.DuueOrderedCompleteness.homEquiv,
    ``Physics.DuueOrderedCompleteness.assemble_apply,
    ``Physics.DuueExchange.antisymmetric_iff,
    ``Physics.DuueExchange.exteriorEquiv,
    ``Physics.DuueExchange.exists_nonzero_iff,
    ``Physics.DuueResidualCompleteness.homEquiv,
    ``Physics.DuueResidualCompleteness.exists_nonzero_iff,
    ``Physics.DuueResidualCompleteness.onFieldsEquiv,
    ``Physics.DuueScalarFlavor.exists_nonzero_iff_charge_trivial,
    ``Physics.DuueScalarFlavor.oneGenerationEquiv,
    ``Physics.DuueScalarFlavor.oneGeneration_finrank,
    ``Math.FiniteInvariantFactor.product_formula,
    ``Math.FourDoubletProductExchange.evaluate_exchange01,
    ``Math.FourDoubletProductExchange.evaluate_exchange12,
    ``Math.FourDoubletProductExchange.braid,
    ``Physics.FourWeakWeylCompleteness.coordinates,
    ``Physics.QqqlExchange.antisymmetric_iff,
    ``Math.FourSlotTripleAlternation.coefficient_slots,
    ``Math.FourSlotTripleSector.slots_ext,
    ``Math.FourSlotTripleSector.coefficient_hasDegree,
    ``Math.FourSlotTripleRestriction.equiv,
    ``Physics.QqqlLocalCompleteness.color_unique,
    ``Physics.QqqlLocalCompleteness.reconstruction,
    ``Physics.QqqlLocalCompleteness.homEquiv,
    ``Physics.QqqlGaugeRegroup.equiv,
    ``Physics.QqqlOrderedCompleteness.homEquiv,
    ``Physics.QqqlOrderedCompleteness.assemble_apply,
    ``Math.FourSlotTripleAlternation.alternates_iff_adjacent,
    ``Physics.QqqlExteriorCompleteness.orderedEquiv,
    ``Physics.QqqlExteriorCompleteness.exteriorEquiv,
    ``Physics.QqqlExteriorCompleteness.exists_nonzero_iff,
    ``Math.FourSlotTripleTransport.equiv,
    ``Physics.QqqlExteriorCompleteness.onFieldsEquiv,
    ``Physics.QqqlScalarFlavor.residualEquiv,
    ``Physics.QqqlScalarFlavor.oneGeneration_finrank,
    ``Physics.OddWeylInvariant.eq_zero,
    ``Physics.OddWeylInvariant.external_eq_zero,
    ``Physics.DeltaLOneSpeciesSupport.gauge_admissible_iff,
    ``Physics.DeltaLOneSpeciesSupport.excluded_candidates_leftSlots,
    ``Physics.QquePhysicalOrderedCompleteness.homEquiv,
    ``Physics.QquePhysicalOrderedCompleteness.assemble_apply,
    ``Physics.QquePhysicalExteriorCompleteness.exteriorEquiv,
    ``Physics.QquePhysicalExteriorCompleteness.onFieldsEquiv,
    ``Physics.QquePhysicalResidualHom.homEquiv,
    ``Physics.QquePhysicalResidualHom.legacyEquiv,
    ``Physics.QquePhysicalResidualHom.exists_nonzero_iff,
    ``Math.ExteriorWeightSupport.circle_weight_zero,
    ``Math.ExteriorWeightSupport.circle_constraint,
    ``Math.FiniteSpeciesExterior.pure_ext,
    ``Math.FiniteSpeciesExterior.orderedRestriction,
    ``Physics.DeltaLOneSignedInput.gauge_candidates,
    ``Physics.DeltaLOneSignedFields.gauge_hypercharge,
    ``Physics.DeltaLOneSignedFields.gauge_center,
    ``Physics.DeltaLOneSignedFields.gauge_candidates,
    ``Physics.OddWeylInvariant.odd_product_ne_one,
    ``Physics.DeltaLOneSignedFields.odd_restriction_vanish,
    ``Physics.DeltaLOneSignedFields.four_candidates,
    ``Physics.DeltaLOneSignedFields.vanish_outside_four,
    ``Physics.DeltaLOneSignedFields.baryonDegree_of_nonzero,
    ``Physics.DeltaLOneSignedFields.no_conjugates_of_nonzero,
    ``Math.FiniteSpeciesProjection.restrict_project,
    ``Math.FiniteSpeciesProjection.partitionEquiv,
    ``Physics.DeltaLOneFourFamilyDecomposition.sector_eq_partition,
    ``Physics.DeltaLOneFourFamilyDecomposition.equiv,
    ``Physics.DeltaLOneFourFamilyDecomposition.nonzero_iff,
    ``Math.FiniteSpeciesExterior.permutation_of_counts,
    ``Math.FiniteSpeciesProjection.pattern_ext,
    ``Physics.DeltaLOneFourFamilyDecomposition.orbit,
    ``Physics.DeltaLOneFourFamilyDecomposition.family_ext,
    ``Physics.DeltaLOneFourFamilyDecomposition.canonical_ext,
    ``Math.ExteriorConjugation.equiv,
    ``Physics.DeltaLOneConjugation.equiv,
    ``Physics.DeltaLOneConjugation.nonzero_iff,
    ``Math.SpeciesPatternAssembly.alternating_pure,
    ``Math.SpeciesPatternAssembly.alternating_vanish,
    ``Math.SpeciesPatternAssembly.restrict_assemble,
    ``Math.SpeciesPatternAssembly.equiv,
    ``Physics.DeltaLOneFamilyCompleteness.duqlEquiv,
    ``Physics.DeltaLOneFamilyCompleteness.qqueEquiv,
    ``Physics.DeltaLOneFamilyCompleteness.qqqlEquiv,
    ``Physics.DeltaLOneFamilyCompleteness.duueEquiv,
    ``Physics.DeltaLOneFamilyCompleteness.stabilizer_card,
    ``Physics.DeltaLOneCoefficientCompleteness.equiv,
    ``Physics.DeltaLOneCoefficientCompleteness.reconstruct_extract,
    ``Physics.DeltaLOneCoefficientCompleteness.extract_reconstruct,
    ``Physics.DeltaLOneCoefficientCompleteness.extract_injective,
    ``Physics.DeltaLOneCoefficientCompleteness.reconstruct_surjective,
    ``Physics.DeltaLOneCoefficientCompleteness.nonzero_iff,
    ``Physics.DeltaLOneCoefficientCompleteness.negativeEquiv,
    ``Physics.DeltaLOneInputTransport.equiv,
    ``Physics.DeltaLOneInputTransport.onFieldsEquiv,
    ``Physics.DeltaLOneRegression.oneGenerationEquiv,
    ``Physics.DeltaLOneRegression.oneGeneration_finrank,
    ``Physics.DeltaLOneRegression.zero_quark_factors,
    ``Physics.DeltaLOneRegression.zero_quark_up,
    ``Physics.DeltaLOneRegression.scalarHom_vanish,
    ``Physics.DeltaLOneRegression.scalar_charge_vanish]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta L one foundations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta L one foundations: {declarations.length} strict transitive axiom checks passed"
