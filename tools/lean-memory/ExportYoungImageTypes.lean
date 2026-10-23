import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungImages
import Lean

/-! Type inventory for comparing the original and optimized Young-image artifacts.
This observer adds no theorem premises. PROOF_TYPES_EXPORT selects its JSON output.
-/

open Lean in
run_cmd do
  let some output ← IO.getEnv "PROOF_TYPES_EXPORT"
    | throwError "Set PROOF_TYPES_EXPORT to a temporary JSON output path"
  let env ← getEnv
  let mut declarations : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungImages then
        declarations := declarations.push (name, info)
  let mut expected : Array String := #[]
  for shape in #[0, 2, 4, 6, 7, 9, 10] do
    for suffix in #[s!"profile{shape}", s!"young{shape}_apply", s!"image{shape}"] do
      expected := expected.push s!"Physics.LiSixQuarkYoungImages.{suffix}"
    for p in [:5] do
      for q in [:5] do
        expected := expected.push s!"Physics.LiSixQuarkYoungImages.image{shape}_entry{p}{q}"
  let mut rows : Array Json := #[]
  for original in expected do
    let foundDecls := declarations.filter fun (name, _) =>
      name.toString == original || name.toString.endsWith ("." ++ original)
    unless foundDecls.size == 1 do
      throwError "Expected exactly one source declaration for {original}, found {foundDecls.size}"
    let some (_, info) := foundDecls[0]?
      | throwError "Missing source declaration for {original}"
    rows := rows.push <| Json.mkObj [("name", toJson original),
      ("type", toJson (toString info.type))]
  IO.FS.writeFile output (Json.compress (toJson rows))
  logInfo m!"Exported {rows.size} source-declared Young-image types"
