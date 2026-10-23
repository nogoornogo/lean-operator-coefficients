import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Batteries.Tactic.Alias
import Lean.Util.FoldConsts
import Lean.Compiler.InlineAttrs

/-! Compile-time checks for deprecated source aliases. Canonical instances
and simp rules are registered once. Checks use the ordinary elaboration
limits. -/

namespace Math.SourceCompatibility
open Lean Elab Command Meta

private def legacyName (name : Name) : Name :=
  name.replacePrefix `Physics `GUT

private def checkAlias (oldName currentName : Name) : TermElabM Unit := do
  let oldInfo ← getConstInfo oldName
  let currentInfo ← getConstInfo currentName
  -- addDecl has already kernel-checked the alias at its declared type. Check
  -- the exact generated value and reverse only genuine direct legacy aliases
  -- in its type; generic unification unfolds large semantic presentations.
  unless oldInfo.levelParams == currentInfo.levelParams &&
      oldInfo.value? (allowOpaque := true) == some (mkConst currentName (oldInfo.levelParams.map mkLevelParam)) do
    throwError "Compatibility value changed: {oldName} / {currentName}"
  let env ← getEnv
  let restored := oldInfo.type.replace fun e => match e with
    | .const name levels =>
      let target := name.replacePrefix `GUT `Physics
      if target != name then
        if let some legacyInfo := env.find? name then
          if legacyInfo.value? (allowOpaque := true) == some (mkConst target (legacyInfo.levelParams.map mkLevelParam)) then
            some (.const target levels)
          else none
        else none
      else none
    | _ => none
  unless restored == currentInfo.type do
    throwError "Compatibility type changed: {oldName} / {currentName}"
  for ax in (← collectAxioms oldName) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Compatibility alias {oldName} uses unexpected axiom {ax}"

/-- Construct aliases in type-dependency order. Retaining legacy heads in
argument types is necessary for old `x.field` notation. -/
private partial def addAlias (pending : NameMap (TSyntax `ident × TSyntax `ident))
    (oldName : Name) (checked : Bool) (visiting : NameSet := {}) : CommandElabM Unit := do
  if (← getEnv).contains oldName then return
  if visiting.contains oldName then throwError "Cyclic compatibility type: {oldName}"
  let some (old, current) := pending.find? oldName
    | throwError "Missing compatibility entry: {oldName}"
  let info ← liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo current
    getConstInfo name
  for used in info.type.getUsedConstants do
    let legacy := legacyName used
    if legacy != used && pending.contains legacy then
      addAlias pending legacy checked (visiting.insert oldName)
  liftTermElabM do
    let env ← getEnv
    let type := info.type.replace fun e => match e with
      | .const name levels =>
        let legacy := legacyName name
        if legacy != name && env.contains legacy then some (.const legacy levels) else none
      | _ => none
    let value := mkConst current.getId (info.levelParams.map mkLevelParam)
    let decl := if wasOriginallyTheorem env current.getId then
      Declaration.thmDecl { info.toConstantVal with
        name := oldName
        type := type
        value := value }
    else
      Declaration.defnDecl { info.toConstantVal with
        name := oldName
        type := type
        value := value
        hints := .abbrev
        safety := if info.isUnsafe then .unsafe else .safe }
    addDecl decl
    unless wasOriginallyTheorem env current.getId do
      Lean.Meta.setInlineAttribute oldName .macroInline
    if isNoncomputable env current.getId then
      modifyEnv (addNoncomputable · oldName)
    else
      if isMarkedMeta env current.getId then modifyEnv (markMeta · oldName)
      compileDecl decl
    addDeclarationRangesFromSyntax oldName (← getRef) old
    Term.addTermInfo' old (← mkConstWithLevelParams oldName) (isBinder := true)
    if checked then checkAlias oldName current.getId
    Batteries.Tactic.Alias.setAliasInfo (.plain current.getId) oldName
    Batteries.Tactic.Alias.addAliasDocstring oldName (.plain current.getId)
  if !wasOriginallyTheorem (← getEnv) current.getId then
    elabCommand (← `(attribute [reducible] $old))
  if info matches .ctorInfo _ then
    elabCommand (← `(attribute [match_pattern] $old))
  elabCommand (← `(attribute [deprecated $current (since := "source-api-v1")] $old))

/-- Create the registered old names without duplicate instances/simp rules.
Each alias is kernel checked, then checked for value equality and axioms. -/
syntax "compatibility_aliases " "[" (ident " => " ident),* "]" : command
-- Large generated facades follow this declaration command with one
-- `assert_compatible` per alias, retaining the default budget for each check.
syntax "compatibility_declarations " "[" (ident " => " ident),* "]" : command
private def aliases (old current : Array (TSyntax `ident)) (checked : Bool) : CommandElabM Unit := do
  let mut pending : NameMap (TSyntax `ident × TSyntax `ident) := {}
  for (a, b) in old.zip current do
    if (← getEnv).contains a.getId then throwError "Legacy name already exists: {a}"
    pending := pending.insert a.getId (a, b)
  for a in old do addAlias pending a.getId checked
  if checked then
    logInfo m!"Compatibility: {old.size} aliases, value/type equalities and strict transitive axiom checks"
  else
    logInfo m!"Compatibility declarations: {old.size} aliases; individual strict checks follow"

elab_rules : command
  | `(compatibility_aliases [$[$old:ident => $current:ident],*]) => do
    aliases old current true
  | `(compatibility_declarations [$[$old:ident => $current:ident],*]) => do
    aliases old current false

/-- Check a value-preserving alias and its strict transitive axiom boundary. -/
elab "assert_compatible " old:ident " => " current:ident : command =>
  liftTermElabM do
    checkAlias old.getId current.getId

end Math.SourceCompatibility
