import Physics.StandardModel.Operators.DipoleControls
import Physics.FieldTheory.Spinor.DistinctFermionCoefficient
import Math.RepresentationTheory.TwoComponentSymmetricSquare
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole completeness imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.NormalizedInvariantFactor.equiv,
    ``Math.NormalizedInvariantFactor.reconstruction,
    ``Math.NormalizedInvariantFactor.exists_nonzero_iff,
    ``Math.NormalizedInvariantFactor.product_unique,
    ``Math.InvariantCoefficientTransport.alongEquiv,
    ``Math.InvariantCoefficientTransport.alongSurjection,
    ``Math.InvariantEvaluation.equiv,
    ``Math.InvariantEvaluation.unique,
    ``Math.TwoComponentSymmetricTensor.squareMatrix_mul,
    ``Math.TwoComponentSymmetricTensor.pair,
    ``Math.TwoComponentTensorUniqueness.unique,
    ``Math.TwoComponentContractions.sl_unique,
    ``Math.TwoComponentContractions.weak_unique,
    ``Math.TwoComponentSymmetricSquare.equiv,
    ``Math.TwoComponentAdjoint.equiv,
    ``Math.TwoComponentAdjoint.conjugation,
    ``Math.TwoComponentTripletDual.equiv,
    ``GUT.DipoleSpinorTensor.normalized,
    ``GUT.DipoleSpinorTensor.unique,
    ``GUT.DipoleGaugeTensor.singlet_unique,
    ``GUT.DipoleGaugeTensor.triplet_unique,
    ``GUT.DipoleGaugeTensor.weakDualEquiv,
    ``GUT.DipoleGaugeTensor.phases,
    ``GUT.DipoleLocalSector.regroupB,
    ``GUT.DipoleLocalSector.regroupW,
    ``GUT.DipoleLocalSector.uniqueB,
    ``GUT.DipoleLocalSector.uniqueW,
    ``GUT.DipoleCoefficientCompleteness.equiv,
    ``GUT.DipoleCoefficientCompleteness.exists_nonzero_iff,
    ``GUT.DipoleSMCoefficient.cancelCharges,
    ``GUT.DipoleSMCoefficient.coefficientEquiv,
    ``GUT.DipoleSMCoefficient.equiv,
    ``GUT.DipoleSMCoefficient.exists_nonzero_iff,
    ``GUT.DipoleSMCoefficient.onFieldsB,
    ``GUT.DipoleSMCoefficient.onFieldsW,
    ``GUT.DipoleFlavorSelection.allowed_iff,
    ``GUT.DipoleFlavorSelection.coefficient_exists_iff_shares,
    ``GUT.DipoleFlavorSelection.forbidden_of_distinct_weights,
    ``GUT.DipoleFlavorSelection.realized_iff,
    ``GUT.DipoleFlavorSelection.realized_of_surjective,
    ``GUT.DipoleFlavorSelection.realized_of_residual_factor,
    ``Math.SelectedCoefficientInputs.exists_nonzero_iff,
    ``Math.SelectedCoefficientInputs.nonzero_of_factorization,
    ``Math.DistinctSpeciesBilinear.reconstruct,
    ``GUT.DistinctFermionCoefficient.alternating,
    ``GUT.DistinctFermionCoefficient.extension_injective,
    ``GUT.DipoleControls.generation_selected,
    ``GUT.DipoleControls.generation_nonzero_iff,
    ``GUT.DipoleControls.generation_not_additive,
    ``GUT.DipoleControls.allowed_not_realized_by_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole completeness: {declarations.length} strict transitive axiom checks passed"
