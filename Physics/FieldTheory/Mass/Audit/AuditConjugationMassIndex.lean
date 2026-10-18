import Physics.FieldTheory.Mass.ConjugationMassIndex
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Arbitrary-group mass/conjugation bridge: strict transitive dependency audit. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Conjugation mass index imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.ConjugationMassIndex.radical_dual_character_invariant,
    ``GUT.ConjugationMassIndex.radical_dual_character_invariant_prod]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conjugation mass index: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conjugation mass index: layer and {declarations.length} strict axiom checks passed"
