import Physics.StandardModel.Operators.WeinbergPermutationCompleteness
import Physics.StandardModel.Operators.DipolePermutationCompleteness
import Physics.StandardModel.Operators.SixQuarkTypedFlavor
import Physics.StandardModel.Operators.DeltaLOneInputTransport
import Physics.StandardModel.Operators.SixQuarkPermutationCompleteness
import Physics.StandardModel.Operators.WeinbergSMInterface
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Lean.Util.CollectAxioms

open Math

/-! Strict audit of the common generator-statistics layer and its first consumers. -/
namespace GUT.StatisticalCompletenessRegression
theorem bosonic_control (z : ℂ) : z ∈ StatisticalCompleteness.sector
    (fun _ : Unit => (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) (fun _ => (1 : ℂ)) := by
  intro j
  simp

theorem fermionic_control (z : ℂ) : z ∈ StatisticalCompleteness.sector
    (fun _ : Unit => (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) (fun _ => (-1 : ℂ)) ↔ z = 0 := by
  constructor
  · intro hz
    have h := hz ()
    change z = (-1 : ℂ) • z at h
    simp only [neg_one_smul] at h
    linear_combination (1 / 2 : ℂ) * h
  · intro hz
    subst z
    intro j
    simp
end GUT.StatisticalCompletenessRegression

run_cmd do
  let declarations := [
    ``GUT.StatisticalCompletenessRegression.bosonic_control,
    ``GUT.StatisticalCompletenessRegression.fermionic_control,
    ``Math.StatisticalCompleteness.statistics_iff,
    ``Math.StatisticalCompleteness.relation_iff,
    ``Math.StatisticalCompleteness.equiv,
    ``Math.StatisticalCompleteness.noExchanges_agrees,
    ``Math.InvariantCoefficientTransport.alongEquiv_compatible,
    ``Math.InvariantCoefficientTransport.alongStatistics,
    ``Math.InvariantCoefficientTransport.alongMaps_compatible,
    ``Math.InvariantCoefficientTransport.alongConstraints,
    ``Math.SixSlotSpeciesTransport.equiv_apply,
    ``Math.SixSlotSpeciesTransport.equiv_symm_apply,
    ``GUT.DipolePermutationCompleteness.equiv_agrees,
    ``GUT.DipolePermutationCompleteness.inverse_agrees,
    ``GUT.QqqlExchange.reconstruct_injective,
    ``GUT.QqqlExchange.local_statistics_iff,
    ``GUT.QqqlExchange.antisymmetric_iff,
    ``GUT.QquePhysicalExteriorCompleteness.permutation_compatible,
    ``GUT.QquePhysicalExteriorCompleteness.permutation_statistics_iff,
    ``GUT.QquePhysicalExteriorCompleteness.orderedEquiv_apply,
    ``GUT.QquePhysicalExteriorCompleteness.orderedEquiv_symm_apply,
    ``GUT.DuueExchange.permutation_compatible,
    ``GUT.DuueExchange.permutation_statistics_iff,
    ``GUT.DuueExchange.orderedEquiv_apply,
    ``GUT.DuueExchange.orderedEquiv_symm_apply,
    ``GUT.DeltaLOneFamilyCompleteness.duqlEquiv_agrees,
    ``GUT.DeltaLOneCoefficientCompleteness.extract_factorization,
    ``GUT.DeltaLOneCoefficientCompleteness.reconstruct_factorization,
    ``GUT.DeltaLOneCoefficientCompleteness.nonzero_coordinates_iff,
    ``Math.SixSlotSpeciesTransport.exists_nonzero_iff,
    ``GUT.WeinbergSMInterface.exists_on_fields_iff,
    ``GUT.DeltaLOneInputTransport.equiv_apply,
    ``GUT.DeltaLOneInputTransport.equiv_symm_apply,
    ``GUT.SixQuarkPermutationCompleteness.compatible,
    ``GUT.SixQuarkPermutationCompleteness.equiv,
    ``GUT.SixQuarkPermutationCompleteness.source_iff,
    ``GUT.SixQuarkPermutationCompleteness.target_iff,
    ``GUT.SixQuarkPermutationCompleteness.extraction,
    ``GUT.SixQuarkPermutationCompleteness.reconstruction,
    ``GUT.SixQuarkPermutationCompleteness.twoProbeEquiv_agrees,
    ``GUT.SixQuarkPermutationCompleteness.inverse_agrees,
    ``Math.FiniteStatisticalFactor.matrix,
    ``Math.FiniteStatisticalFactor.compatible,
    ``Math.FiniteStatisticalFactor.equiv,
    ``Math.NormalizedStatisticalFactor.compatible,
    ``Math.NormalizedStatisticalFactor.equiv,
    ``GUT.WeinbergPermutationCompleteness.localSwap_scalar,
    ``GUT.WeinbergPermutationCompleteness.target_symmetric_iff,
    ``GUT.WeinbergPermutationCompleteness.source_sector_iff,
    ``GUT.WeinbergPermutationCompleteness.symmetricEquiv_agrees,
    ``GUT.WeinbergPermutationCompleteness.homEquiv_agrees,
    ``GUT.WeinbergModelSector.homEquiv_agrees,
    ``GUT.WeinbergModelSector.inverse_agrees,
    ``GUT.WeinbergSMInterface.onFieldsEquiv,
    ``GUT.SixQuarkFlavorCoordinates.typed_statistics_iff,
    ``GUT.SixQuarkTypedFlavor.statistics_iff]
  let declarations := declarations ++ [
    ``GUT.SixQuarkTypedFlavor.homLinearEquiv_apply,
    ``GUT.SixQuarkTypedFlavor.homLinearEquiv_symm_apply,
    ``GUT.DeltaBTwoFlavorBridge.sectorHomEquiv_apply,
    ``GUT.DeltaBTwoFlavorBridge.sectorHomEquiv_symm_apply,
    ``GUT.DeltaBTwoFlavorBridge.onFieldsHomEquiv_symm_apply,
    ``GUT.DeltaLOneInputTransport.onFieldsEquiv,
    ``GUT.DipoleSMCoefficient.onFieldsB,
    ``GUT.DipoleSMCoefficient.onFieldsW]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Statistical completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Statistical completeness: {declarations.length} strict transitive axiom checks passed"
