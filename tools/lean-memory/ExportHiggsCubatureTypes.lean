import Math.Algebra.HiggsFourWaveCubature.Sorted
import Lean

/-! Compatibility observation only; exports the 420 unchanged family entry types. -/
open Lean in
run_cmd do
  let some output ← IO.getEnv "HIGGS_CUBATURE_TYPE_EXPORT"
    | throwError "Set HIGGS_CUBATURE_TYPE_EXPORT to a temporary JSON output path"
  let env ← getEnv
  let mut rows : Array Json := #[]
  for r in [:3] do
    for m in [:35] do
      for i in [:4] do
        let name := Name.str `Math.HiggsFourWaveCubature s!"moments{r}_{m}_{i}"
        let some info := env.find? name | throwError "Missing family theorem {name}"
        rows := rows.push (Json.mkObj [("name",toJson name.toString),
          ("type",toJson (reprStr info.type))])
  IO.FS.writeFile output (Json.arr rows).compress
  logInfo m!"Exported {rows.size} family theorem types"
