import Math.LinearAlgebra.Symmetric.SmallSymmetricRank
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``SmallSymmetricRank.star_rank,
    ``SmallSymmetricRank.singlet_rank, ``SmallSymmetricRank.blockKernelEquiv,
    ``SmallSymmetricRank.matrix_nullity, ``SmallSymmetricRank.block_nullity,
    ``SmallSymmetricRank.block_nullity_cases, ``SmallSymmetricRank.nonzero_coefficients_rank_drop]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Small symmetric rank: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Small symmetric rank: {declarations.length} strict axiom checks passed"
