import Physics.StandardModel.Operators.Dipole.DipoleControls
import Physics.FieldTheory.Spinor.Weyl.DistinctFermionCoefficient
import Math.RepresentationTheory.Symmetric.TwoComponentSymmetricSquare
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
    ``Physics.DipoleSpinorTensor.normalized,
    ``Physics.DipoleSpinorTensor.unique,
    ``Physics.DipoleGaugeTensor.singlet_unique,
    ``Physics.DipoleGaugeTensor.triplet_unique,
    ``Physics.DipoleGaugeTensor.weakDualEquiv,
    ``Physics.DipoleGaugeTensor.phases,
    ``Physics.DipoleLocalSector.regroupB,
    ``Physics.DipoleLocalSector.regroupW,
    ``Physics.DipoleLocalSector.uniqueB,
    ``Physics.DipoleLocalSector.uniqueW,
    ``Physics.DipoleCoefficientCompleteness.equiv,
    ``Physics.DipoleCoefficientCompleteness.exists_nonzero_iff,
    ``Physics.DipoleSMCoefficient.cancelCharges,
    ``Physics.DipoleSMCoefficient.coefficientEquiv,
    ``Physics.DipoleSMCoefficient.equiv,
    ``Physics.DipoleSMCoefficient.exists_nonzero_iff,
    ``Physics.DipoleSMCoefficient.onFieldsB,
    ``Physics.DipoleSMCoefficient.onFieldsW,
    ``Physics.DipoleFlavorSelection.allowed_iff,
    ``Physics.DipoleFlavorSelection.coefficient_exists_iff_shares,
    ``Physics.DipoleFlavorSelection.forbidden_of_distinct_weights,
    ``Physics.DipoleFlavorSelection.realized_iff,
    ``Physics.DipoleFlavorSelection.realized_of_surjective,
    ``Physics.DipoleFlavorSelection.realized_of_residual_factor,
    ``Math.SelectedCoefficientInputs.exists_nonzero_iff,
    ``Math.SelectedCoefficientInputs.nonzero_of_factorization,
    ``Math.DistinctSpeciesBilinear.reconstruct,
    ``Physics.DistinctFermionCoefficient.alternating,
    ``Physics.DistinctFermionCoefficient.extension_injective,
    ``Physics.DipoleControls.generation_selected,
    ``Physics.DipoleControls.generation_nonzero_iff,
    ``Physics.DipoleControls.generation_not_additive,
    ``Physics.DipoleControls.allowed_not_realized_by_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole completeness: {declarations.length} strict transitive axiom checks passed"
