import Math.RepresentationTheory.Characters.PositiveCharacterQuotient
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Actual equivariant quotients, not assumed character classification. -/

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Positive quotient imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.PositiveCharacterQuotient.hom_finrank_add,
    ``Math.PositiveCharacterQuotient.exists_surjective_of_character_add_of_nonzero,
    ``Math.PositiveCharacterQuotient.exists_surjective_of_character_add]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Positive quotient: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Positive quotient: layer and {declarations.length} strict axiom checks passed"
