import Physics.StandardModel.Operators.SMConstantContentRanks

/-! CSV export from the executable classifier with its universally proved soundness theorem. -/
open GUT

def main : IO Unit := do
  IO.println "species,fermions,m,delta,columns,rank,status"
  for s in List.finRange 10 do
    for n in List.range (SMConstantContentRanks.dimension s + 1) do
      if n > 0 then
        for m in List.range (n * SMWeakWeightBasis.doubletCount s + 1) do
          for t in List.range (m + 1) do
            let delta := (m : Int) - 2 * (t : Int)
            let columns := SMConstantContentRanks.columns s n m
            let result := SMConstantContentRanks.evaluate s n m delta
            let rank := result.map toString |>.getD ""
            let status := if n % 2 != 0 then "odd_full"
              else if (n : Int) * DeltaLOneSignedInput.hypercharge s + 3 * delta != 0 then "charged_full"
              else if result.isSome then "llhh" else "unclassified"
            IO.println s!"{s.val},{n},{m},{delta},{columns},{rank},{status}"

#eval main
