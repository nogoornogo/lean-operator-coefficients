import Math.RepresentationTheory.Multiplicity.BalancedMultiplicityExtension
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Balanced multiplicities import upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.BalancedMultiplicityExtension.character_prod,
    ``Math.BalancedMultiplicityExtension.index_eq,
    ``Math.BalancedMultiplicityExtension.refl,
    ``Math.BalancedMultiplicityExtension.negative_finrank,
    ``Math.BalancedMultiplicityExtension.opposite_nonzero,
    ``Math.BalancedMultiplicityExtension.index_eq_trans]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Balanced multiplicities: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Balanced multiplicities: {declarations.length} strict axiom checks passed"
