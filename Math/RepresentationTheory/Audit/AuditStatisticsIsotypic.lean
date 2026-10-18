import Math.RepresentationTheory.TensorStatisticsIsotypic
import Math.RepresentationTheory.RelationStatisticsIsotypic
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.IsotypicResidual.stable,
    ``Math.IsotypicResidual.sumEquiv,
    ``Math.IsotypicResidual.sumEquiv_single,
    ``Math.IsotypicResidual.sumEquiv_symm_component,
    ``Math.CommutingStatisticsModule.action,
    ``Math.CommutingStatisticsModule.action_apply,
    ``Math.CommutingStatisticsModule.equiv,
    ``Math.CommutingStatisticsModule.equiv_single,
    ``Math.DirectSumResidualHom.equiv,
    ``Math.DirectSumResidualHom.coefficientEquiv,
    ``Math.CommutingStatisticsModule.coefficientEquiv,
    ``Math.CommutingStatisticsModule.coefficientEquiv_apply,
    ``Math.CommutingStatisticsModule.coefficient_zero_iff,
    ``Math.IsotypicClassMap.componentClass_injective,
    ``Math.SpechtIsotypicLabels.partitionClass_bijective,
    ``Math.SpechtIsotypicLabels.label_simple_iff,
    ``Math.SpechtIsotypicLabels.supportedEquiv,
    ``Math.SpechtIsotypicLabels.finite_components,
    ``Math.TensorStatisticsIsotypic.equiv,
    ``Math.TensorStatisticsIsotypic.partitionCoefficientEquiv,
    ``Math.TensorStatisticsIsotypic.coefficient_zero_iff,
    ``Math.RelationStatisticsIsotypic.quotient_commutes,
    ``Math.RelationStatisticsIsotypic.coefficientEquiv]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Statistics isotypic: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Statistics isotypic: {declarations.length} strict transitive checks passed"
