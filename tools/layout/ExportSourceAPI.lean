import GUT

/-! Inventory tool, not a theorem premise. Run only after a successful complete
build of the branch being inventoried. SOURCE_API_EXPORT selects a temporary
output file; the frozen plan and rebuilt consumer checks own migration evidence. -/

open Lean in
run_cmd do
  let some output ← IO.getEnv "SOURCE_API_EXPORT"
    | throwError "Set SOURCE_API_EXPORT to a temporary JSON output path"
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`Math).isPrefixOf mod || (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
        let kind := match info with
          | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
        rows := rows.push <| Json.mkObj [("name", toJson name.toString),
          ("module", toJson mod.toString), ("kind", toJson kind),
          ("unsafe", toJson info.isUnsafe)]
  IO.FS.writeFile output (Json.compress (toJson rows))
  logInfo m!"Exported {rows.size} repository constants"
