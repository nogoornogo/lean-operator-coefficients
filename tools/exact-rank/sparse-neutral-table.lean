import Physics.StandardModel.Operators.SMNeutralSparseRanks

/-! Compiled exact evaluation; the soundness theorem retains explicit Weyl input.
Numeric output alone is not a kernel-checked arithmetic certificate. -/
open GUT
def main : IO Unit := do
  let cache := SMKernelWeightData.tables
  IO.println "species,fermions,m,delta,columns,multiplicity,rank"
  for r in SMNeutralSparseRanks.inputs do
    let answer := SMNeutralSparseRanks.solveDirectWith cache r
    let columns := SMConstantContentRanks.columns r.species r.fermions r.m
    IO.println s!"{r.species.val},{r.fermions},{r.m},{r.delta},{columns},{answer.multiplicity},{answer.rank}"

#eval main
