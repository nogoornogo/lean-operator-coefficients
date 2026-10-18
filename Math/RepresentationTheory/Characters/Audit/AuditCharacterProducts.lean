import Math.RepresentationTheory.Characters.CharacterProducts
import Lean.Util.CollectAxioms
run_cmd do
  for ax in (← Lean.collectAxioms ``Math.CharacterProducts.prod_character) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Character product uses unexpected axiom {ax}"
  Lean.logInfo "Character products: 1 strict transitive check passed"
