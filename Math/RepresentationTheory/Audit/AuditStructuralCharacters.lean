import Math.RepresentationTheory.ExteriorCharacterPolynomial
import Math.RepresentationTheory.SU2WeightExtraction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Structural character audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.ExteriorCharacterPolynomial.coeff_insert,
    ``Math.ExteriorCharacterPolynomial.generating_coeff,
    ``Math.ExteriorCharacterPolynomial.exterior_character,
    ``Math.SU2WeightExtraction.pairCharacter_torus,
    ``Math.SU2WeightExtraction.integral_pairCharacter,
    ``Math.SU2WeightExtraction.integral_of_weight_expansion,
    ``Math.SU2WeightExtraction.invariant_finrank,
    ``Math.SU2WeightExtraction.integral_pair_of_weight_expansion]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Structural character audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Structural characters: layer and {ds.length} strict transitive checks passed"
