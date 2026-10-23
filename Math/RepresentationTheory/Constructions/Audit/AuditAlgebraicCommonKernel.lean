import Math.RepresentationTheory.Decomposition.AlgebraicCommonKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Math.AlgebraicCommonKernel.simple,
    ``Math.AlgebraicCommonKernel.simple_spec,
    ``Math.AlgebraicCommonKernel.targetComponent,
    ``Math.AlgebraicCommonKernel.simpleInclusion,
    ``Math.AlgebraicCommonKernel.assemble_injective,
    ``Math.AlgebraicCommonKernel.exists_uninjective_component,
    ``Math.AlgebraicCommonKernel.exists_common_simple_kernel]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"Math.AlgebraicCommonKernel: {declarations.length} strict transitive axiom checks passed"
