import Math.Audit.ImportOrigin
import Math.LieGroups.SpecialUnitary.Matter
import Math.LinearAlgebra.ExteriorEigenbasisTrace

/-! The arbitrary-rank SU block and matter construction must not import
an SU(5)/SU(6) source, branching theorem, or physical model. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Generic SU(n) construction imports a fixed-rank model: {mod}"

#print axioms Math.SUN.Block.rawMatrix_unitary
#print axioms Math.SUN.Block.rawMatrix_det
#print axioms Math.SUN.Block.matrixHom_unitary
#print axioms Math.SUN.Block.matrixHom_det
#print axioms Math.SUN.Block.inclusion
#print axioms Math.SUN.Block.inclusion_injective
#print axioms Math.SUN.Block.inclusion_continuous
#print axioms Math.SUN.Block.continuousInclusion
#print axioms Math.SUN.Block.inclusion_left
#print axioms Math.SUN.Block.inclusion_right
#print axioms Math.SUN.Block.inclusion_zero
#print axioms Math.SUN.Block.dimension_parameter
#print axioms Math.SUN.Block.exists_inclusion
#print axioms Math.SUN.Matter.dualEquiv
#print axioms Math.SUN.Matter.wedgeEquiv
#print axioms Math.SUN.Matter.dual_unitary
#print axioms Math.SUN.Matter.wedge_unitary
#print axioms Math.SUN.Matter.dual_continuous
#print axioms Math.SUN.Matter.wedge_continuous
#print axioms Math.ExteriorEigenbasisTrace.trace_eq_sum
#print axioms Math.ExteriorEigenbasisTrace.product_ordered
#print axioms Math.ExteriorEigenbasisTrace.exterior_eigen
#print axioms Math.ExteriorEigenbasisTrace.exterior_trace
