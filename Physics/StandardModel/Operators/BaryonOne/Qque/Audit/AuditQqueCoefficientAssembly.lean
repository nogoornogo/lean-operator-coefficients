import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientAssembly
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueResidualHom
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientSector
import Physics.FieldTheory.Spinor.Weyl.WeylSpinorUniqueness
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientCompleteness
import Math.RepresentationTheory.Symmetric.SymmetricSquareDescent
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Qque coefficient assembly imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.SymmetricSquareDescent.equiv,
    ``Math.SymmetricSquareDescent.equivariantEquiv,
    ``Physics.QqueCoefficientAssembly.probe,
    ``Physics.QqueCoefficientAssembly.assembleLinear,
    ``Physics.QqueCoefficientAssembly.injective_on_symmetric,
    ``Physics.QqueCoefficientAssembly.symmetricAssembly_injective,
    ``Physics.QqueCoefficientAssembly.assemble_nonzero_iff,
    ``Physics.QqueCoefficientAssembly.exists_on_fields,
    ``Math.InvariantTensorCurry.equiv,
    ``Math.InvariantTensorCurry.dualTensorDual,
    ``Math.TensorSquareMultilinear.symmetricSquareEquiv,
    ``Physics.QqueResidualHom.equiv,
    ``Physics.QqueResidualHom.assembly_injective,
    ``Physics.QqueResidualHom.assembly_nonzero_iff,
    ``Physics.QqueResidualHom.exists_on_fields,
    ``Math.FourSlotSpeciesDegree.coefficient_hasDegree,
    ``Physics.QqueCoefficientSector.alternation_mem,
    ``Physics.QqueCoefficientSector.fromHom_injective,
    ``Math.FourSlotSpeciesRestriction.slots_ext,
    ``Math.FourSlotRestrictionLift.restriction,
    ``Math.FourSlotRestrictionLift.restriction_swap,
    ``Math.FourSlotRestrictionLift.reconstruct,
    ``Math.FourSlotRestrictionLift.exists_ordered,
    ``Physics.QqueCoefficientSector.exists_ordered,
    ``Physics.WeylSpinorUniqueness.eq_smul_four,
    ``Physics.SMEpsilonUniqueness.weak_unique,
    ``Physics.SMEpsilonUniqueness.color_unique,
    ``Physics.QqueGaugeUniqueness.eq_smul_qque,
    ``Math.ExternalInvariantFactorization.factor_right,
    ``Math.ExternalInvariantFactorization.factor_left,
    ``Physics.QqueSpinorFactorization.reconstruct,
    ``Physics.QqueGaugeFactorization.reconstruct,
    ``Math.FourSlotSpeciesTransport.equiv,
    ``Physics.QqueCoefficientSector.hasNonzeroAlternation_iff,
    ``Physics.QqueCoefficientCompleteness.residual_symmetric,
    ``Physics.QqueCoefficientCompleteness.reconstruct,
    ``Physics.QqueCoefficientCompleteness.fromHom_surjective,
    ``Physics.QqueCoefficientCompleteness.equiv,
    ``Physics.QqueCoefficientCompleteness.onFieldsEquiv,
    ``Physics.QqueCoefficientCompleteness.exists_on_fields_iff,
    ``Physics.QqueCoefficientCompleteness.hasNonzeroAlternation_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Qque coefficient assembly: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Qque coefficient assembly: {declarations.length} strict axiom checks passed"
