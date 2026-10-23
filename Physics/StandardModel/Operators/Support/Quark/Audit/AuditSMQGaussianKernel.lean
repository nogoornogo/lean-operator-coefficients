import Physics.StandardModel.Operators.Support.Coordinates.SMConstantFullSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Exact local coordinate audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMRationalLocalKernel.exhaustive,
    ``Physics.SMRationalLocalKernel.coefficientEquiv,
    ``Physics.SMGaussianLocalData.spin_embed,
    ``Physics.SMGaussianLocalData.color_embed,
    ``Physics.SMGaussianLocalData.weak_embed,
    ``Physics.SMGaussianLocalData.phase_embed,
    ``Physics.SMGaussianLocalData.spin_data_embed,
    ``Physics.SMQExactCoordinates.field_sample_coordinate,
    ``Physics.SMQExactCoordinates.boson_sample_coordinate,
    ``Physics.SMQExactCoordinates.action_sample_coordinate,
    ``Physics.SMQGaussianKernel.matrix_semantics,
    ``Physics.SMQGaussianKernel.coefficient_dimension,
    ``Physics.SMQGaussianKernel.allowed_iff,
    ``Physics.SMQGaussianKernel.kernel_dimension,
    ``Physics.SMQGaussianKernel.rank_add_nullity,
    ``Physics.SMQGaussianKernel.nullity_above_capacity,
    ``Physics.SMQGaussianKernel.forbidden_odd,
    ``Physics.SMQGaussianKernel.forbidden_charged,
    ``Physics.SMQConjugateKernel.coefficientEquiv,
    ``Physics.SMQConjugateKernel.coefficient_dimension,
    ``Physics.SMQConjugateKernel.allowed_iff,
    ``Physics.SMQConjugateKernel.kernel_dimension,
    ``Physics.SMQConjugateKernel.rank_add_nullity,
    ``Physics.SMConstantFullSupport.testEquiv,
    ``Physics.SMConstantFullSupport.quark_allowed_iff,
    ``Physics.SMConstantFullSupport.conjugate_quark_allowed_iff,
    ``Physics.SMConstantFullSupport.lepton_allowed_iff,
    ``Physics.SMConstantFullSupport.conjugate_lepton_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact local coordinates: layer and {ds.length} strict transitive checks passed"
