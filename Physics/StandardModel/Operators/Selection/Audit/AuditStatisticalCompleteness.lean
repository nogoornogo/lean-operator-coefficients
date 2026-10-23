import Physics.StandardModel.Operators.Weinberg.WeinbergPermutationCompleteness
import Physics.StandardModel.Operators.Dipole.DipolePermutationCompleteness
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTypedFlavor
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneInputTransport
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkPermutationCompleteness
import Physics.StandardModel.Operators.Weinberg.WeinbergSMInterface
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorBridge
import Lean.Util.CollectAxioms

open Math

/-! Strict audit of the common generator-statistics layer and its first consumers. -/
namespace Physics.StatisticalCompletenessRegression
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
end Physics.StatisticalCompletenessRegression

run_cmd do
  let declarations := [
    ``Physics.StatisticalCompletenessRegression.bosonic_control,
    ``Physics.StatisticalCompletenessRegression.fermionic_control,
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
    ``Physics.DipolePermutationCompleteness.equiv_agrees,
    ``Physics.DipolePermutationCompleteness.inverse_agrees,
    ``Physics.QqqlExchange.reconstruct_injective,
    ``Physics.QqqlExchange.local_statistics_iff,
    ``Physics.QqqlExchange.antisymmetric_iff,
    ``Physics.QquePhysicalExteriorCompleteness.permutation_compatible,
    ``Physics.QquePhysicalExteriorCompleteness.permutation_statistics_iff,
    ``Physics.QquePhysicalExteriorCompleteness.orderedEquiv_apply,
    ``Physics.QquePhysicalExteriorCompleteness.orderedEquiv_symm_apply,
    ``Physics.DuueExchange.permutation_compatible,
    ``Physics.DuueExchange.permutation_statistics_iff,
    ``Physics.DuueExchange.orderedEquiv_apply,
    ``Physics.DuueExchange.orderedEquiv_symm_apply,
    ``Physics.DeltaLOneFamilyCompleteness.duqlEquiv_agrees,
    ``Physics.DeltaLOneCoefficientCompleteness.extract_factorization,
    ``Physics.DeltaLOneCoefficientCompleteness.reconstruct_factorization,
    ``Physics.DeltaLOneCoefficientCompleteness.nonzero_coordinates_iff,
    ``Math.SixSlotSpeciesTransport.exists_nonzero_iff,
    ``Physics.WeinbergSMInterface.exists_on_fields_iff,
    ``Physics.DeltaLOneInputTransport.equiv_apply,
    ``Physics.DeltaLOneInputTransport.equiv_symm_apply,
    ``Physics.SixQuarkPermutationCompleteness.compatible,
    ``Physics.SixQuarkPermutationCompleteness.equiv,
    ``Physics.SixQuarkPermutationCompleteness.source_iff,
    ``Physics.SixQuarkPermutationCompleteness.target_iff,
    ``Physics.SixQuarkPermutationCompleteness.extraction,
    ``Physics.SixQuarkPermutationCompleteness.reconstruction,
    ``Physics.SixQuarkPermutationCompleteness.twoProbeEquiv_agrees,
    ``Physics.SixQuarkPermutationCompleteness.inverse_agrees,
    ``Math.FiniteStatisticalFactor.matrix,
    ``Math.FiniteStatisticalFactor.compatible,
    ``Math.FiniteStatisticalFactor.equiv,
    ``Math.NormalizedStatisticalFactor.compatible,
    ``Math.NormalizedStatisticalFactor.equiv,
    ``Physics.WeinbergPermutationCompleteness.localSwap_scalar,
    ``Physics.WeinbergPermutationCompleteness.target_symmetric_iff,
    ``Physics.WeinbergPermutationCompleteness.source_sector_iff,
    ``Physics.WeinbergPermutationCompleteness.symmetricEquiv_agrees,
    ``Physics.WeinbergPermutationCompleteness.homEquiv_agrees,
    ``Physics.WeinbergModelSector.homEquiv_agrees,
    ``Physics.WeinbergModelSector.inverse_agrees,
    ``Physics.WeinbergSMInterface.onFieldsEquiv,
    ``Physics.SixQuarkFlavorCoordinates.typed_statistics_iff,
    ``Physics.SixQuarkTypedFlavor.statistics_iff]
  let declarations := declarations ++ [
    ``Physics.SixQuarkTypedFlavor.homLinearEquiv_apply,
    ``Physics.SixQuarkTypedFlavor.homLinearEquiv_symm_apply,
    ``Physics.DeltaBTwoFlavorBridge.sectorHomEquiv_apply,
    ``Physics.DeltaBTwoFlavorBridge.sectorHomEquiv_symm_apply,
    ``Physics.DeltaBTwoFlavorBridge.onFieldsHomEquiv_symm_apply,
    ``Physics.DeltaLOneInputTransport.onFieldsEquiv,
    ``Physics.DipoleSMCoefficient.onFieldsB,
    ``Physics.DipoleSMCoefficient.onFieldsW]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Statistical completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Statistical completeness: {declarations.length} strict transitive axiom checks passed"
