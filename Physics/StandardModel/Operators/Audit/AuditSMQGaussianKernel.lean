import Physics.StandardModel.Operators.SMConstantFullSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Exact local coordinate audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.SMRationalLocalKernel.exhaustive,
    ``GUT.SMRationalLocalKernel.coefficientEquiv,
    ``GUT.SMGaussianLocalData.spin_embed,
    ``GUT.SMGaussianLocalData.color_embed,
    ``GUT.SMGaussianLocalData.weak_embed,
    ``GUT.SMGaussianLocalData.phase_embed,
    ``GUT.SMGaussianLocalData.spin_data_embed,
    ``GUT.SMQExactCoordinates.field_sample_coordinate,
    ``GUT.SMQExactCoordinates.boson_sample_coordinate,
    ``GUT.SMQExactCoordinates.action_sample_coordinate,
    ``GUT.SMQGaussianKernel.matrix_semantics,
    ``GUT.SMQGaussianKernel.coefficient_dimension,
    ``GUT.SMQGaussianKernel.allowed_iff,
    ``GUT.SMQGaussianKernel.kernel_dimension,
    ``GUT.SMQGaussianKernel.rank_add_nullity,
    ``GUT.SMQGaussianKernel.nullity_above_capacity,
    ``GUT.SMQGaussianKernel.forbidden_odd,
    ``GUT.SMQGaussianKernel.forbidden_charged,
    ``GUT.SMQConjugateKernel.coefficientEquiv,
    ``GUT.SMQConjugateKernel.coefficient_dimension,
    ``GUT.SMQConjugateKernel.allowed_iff,
    ``GUT.SMQConjugateKernel.kernel_dimension,
    ``GUT.SMQConjugateKernel.rank_add_nullity,
    ``GUT.SMConstantFullSupport.testEquiv,
    ``GUT.SMConstantFullSupport.quark_allowed_iff,
    ``GUT.SMConstantFullSupport.conjugate_quark_allowed_iff,
    ``GUT.SMConstantFullSupport.lepton_allowed_iff,
    ``GUT.SMConstantFullSupport.conjugate_lepton_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact local coordinates: layer and {ds.length} strict transitive checks passed"
