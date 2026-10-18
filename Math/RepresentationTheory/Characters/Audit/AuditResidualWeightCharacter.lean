import Math.RepresentationTheory.Characters.ResidualWeightCharacter
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Residual weights import application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.ResidualWeightSpace.sector,
    ``Math.ResidualWeightSpace.actions_commute,
    ``Math.ResidualWeightSpace.representation_apply,
    ``Math.ResidualWeightSpace.product_on_weight,
    ``Math.ResidualWeightSpace.product_restrict,
    ``Math.ResidualWeightSpace.character_expansion,
    ``Math.ResidualWeightCharacter.eval_injective,
    ``Math.ResidualWeightCharacter.dual_apply,
    ``Math.ResidualWeightCharacter.eval_dual,
    ``Math.ResidualWeightCharacter.coeff_comp_eq_of_eval_invariant,
    ``Math.ResidualWeightCharacter.coefficients_apply,
    ``Math.ResidualWeightCharacter.eval_coefficients,
    ``Math.ResidualWeightCharacter.dualCoefficients_apply,
    ``Math.ResidualWeightCharacter.eval_dualCoefficients,
    ``Math.ResidualWeightCharacter.index_invariant]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Residual weights: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Residual weights: layer and {declarations.length} strict axiom checks passed"
