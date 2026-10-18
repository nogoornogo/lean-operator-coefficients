import Math.RepresentationTheory.Unitary.ContinuousDual
import Math.RepresentationTheory.Characters.ResidualWeightContinuity
import Math.RepresentationTheory.Characters.CompactPositiveCharacterQuotient
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Compact light continuity imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.ContinuousDual.jointlyContinuous_dual,
    ``Math.ResidualWeightContinuity.subrepresentation,
    ``Math.ResidualWeightContinuity.weight,
    ``Math.CompactIrreducibleQuotient.semisimple,
    ``Math.CompactIrreducibleQuotient.exists_irreducible_quotient,
    ``Math.CompactPositiveCharacterQuotient.exists_surjective_of_character_add_of_nonzero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Compact light continuity: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Compact light continuity: layer and {declarations.length} strict axiom checks passed"
