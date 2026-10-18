import Physics.StandardModel.Operators.QqueCoefficientAssembly
import Physics.StandardModel.Operators.QqueResidualHom
import Physics.StandardModel.Operators.QqueCoefficientSector
import Physics.FieldTheory.Spinor.WeylSpinorUniqueness
import Physics.StandardModel.Operators.QqueCoefficientCompleteness
import Math.RepresentationTheory.SymmetricSquareDescent
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
    ``GUT.QqueCoefficientAssembly.probe,
    ``GUT.QqueCoefficientAssembly.assembleLinear,
    ``GUT.QqueCoefficientAssembly.injective_on_symmetric,
    ``GUT.QqueCoefficientAssembly.symmetricAssembly_injective,
    ``GUT.QqueCoefficientAssembly.assemble_nonzero_iff,
    ``GUT.QqueCoefficientAssembly.exists_on_fields,
    ``Math.InvariantTensorCurry.equiv,
    ``Math.InvariantTensorCurry.dualTensorDual,
    ``Math.TensorSquareMultilinear.symmetricSquareEquiv,
    ``GUT.QqueResidualHom.equiv,
    ``GUT.QqueResidualHom.assembly_injective,
    ``GUT.QqueResidualHom.assembly_nonzero_iff,
    ``GUT.QqueResidualHom.exists_on_fields,
    ``Math.FourSlotSpeciesDegree.coefficient_hasDegree,
    ``GUT.QqueCoefficientSector.alternation_mem,
    ``GUT.QqueCoefficientSector.fromHom_injective,
    ``Math.FourSlotSpeciesRestriction.slots_ext,
    ``Math.FourSlotRestrictionLift.restriction,
    ``Math.FourSlotRestrictionLift.restriction_swap,
    ``Math.FourSlotRestrictionLift.reconstruct,
    ``Math.FourSlotRestrictionLift.exists_ordered,
    ``GUT.QqueCoefficientSector.exists_ordered,
    ``GUT.WeylSpinorUniqueness.eq_smul_four,
    ``GUT.SMEpsilonUniqueness.weak_unique,
    ``GUT.SMEpsilonUniqueness.color_unique,
    ``GUT.QqueGaugeUniqueness.eq_smul_qque,
    ``Math.ExternalInvariantFactorization.factor_right,
    ``Math.ExternalInvariantFactorization.factor_left,
    ``GUT.QqueSpinorFactorization.reconstruct,
    ``GUT.QqueGaugeFactorization.reconstruct,
    ``Math.FourSlotSpeciesTransport.equiv,
    ``GUT.QqueCoefficientSector.hasNonzeroAlternation_iff,
    ``GUT.QqueCoefficientCompleteness.residual_symmetric,
    ``GUT.QqueCoefficientCompleteness.reconstruct,
    ``GUT.QqueCoefficientCompleteness.fromHom_surjective,
    ``GUT.QqueCoefficientCompleteness.equiv,
    ``GUT.QqueCoefficientCompleteness.onFieldsEquiv,
    ``GUT.QqueCoefficientCompleteness.exists_on_fields_iff,
    ``GUT.QqueCoefficientCompleteness.hasNonzeroAlternation_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Qque coefficient assembly: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Qque coefficient assembly: {declarations.length} strict axiom checks passed"
