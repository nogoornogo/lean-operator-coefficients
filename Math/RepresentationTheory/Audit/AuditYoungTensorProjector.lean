import Math.RepresentationTheory.YoungTensorProjector
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.TensorPermutationStatistics.commutes,
    ``Math.TensorPermutationStatistics.permutation_tprod,
    ``Math.TensorPermutationStatistics.symmetricQuotientEquiv,
    ``Math.TensorPermutationStatistics.alternatingQuotientEquiv,
    ``Math.TensorPermutationStatistics.alternating_condition,
    ``Math.YoungTensorProjector.normalized_idempotent,
    ``Math.YoungTensorProjector.projector,
    ``Math.YoungTensorProjector.projector_idempotent,
    ``Math.YoungTensorProjector.projector_twice,
    ``Math.YoungTensorProjector.range_stable,
    ``Math.YoungTensorProjector.kernel_stable,
    ``Math.YoungTensorProjector.quotientEquiv,
    ``Math.YoungTensorProjector.kernel_eq_relations,
    ``Math.YoungTensorProjector.range_kernel_complement]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Young tensor projector: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Young tensor projector: {declarations.length} strict transitive checks passed"
