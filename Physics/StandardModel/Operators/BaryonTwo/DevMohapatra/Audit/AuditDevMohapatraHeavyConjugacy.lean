import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyConjugacy
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyConjugacy imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraHeavyConjugacy.adj,
    ``Physics.DevMohapatraHeavyConjugacy.field_involutive,
    ``Physics.DevMohapatraHeavyConjugacy.adj_involutive,
    ``Physics.DevMohapatraHeavyConjugacy.adj_mul,
    ``Physics.DevMohapatraHeavyConjugacy.adj_smul,
    ``Physics.DevMohapatraHeavyConjugacy.adj_add,
    ``Physics.DevMohapatraHeavyConjugacy.adj_sub,
    ``Physics.DevMohapatraHeavyConjugacy.adj_neg,
    ``Physics.DevMohapatraHeavyConjugacy.adj_zero,
    ``Physics.DevMohapatraHeavyConjugacy.include_adj,
    ``Physics.DevMohapatraHeavyConjugacy.include_injective,
    ``Physics.DevMohapatraHeavyConjugacy.adj_current,
    ``Physics.DevMohapatraHeavyConjugacy.adj_bar_current,
    ``Physics.DevMohapatraHeavyConjugacy.field_bar_u,
    ``Physics.DevMohapatraHeavyConjugacy.adj_cross,
    ``Physics.DevMohapatraHeavyConjugacy.conjugated,
    ``Physics.DevMohapatraHeavyConjugacy.residual_conjugated,
    ``Physics.DevMohapatraHeavyConjugacy.solution_conjugated,
    ``Physics.DevMohapatraHeavyConjugacy.solution_adjoint,
    ``Physics.DevMohapatraHeavyConjugacy.adj_generator,
    ``Physics.DevMohapatraHeavyConjugacy.adj_sum,
    ``Physics.DevMohapatraHeavyConjugacy.evaluate_conjugate_generator,
    ``Physics.DevMohapatraHeavyConjugacy.evaluate_hc,
    ``Physics.DevMohapatraHeavyConjugacy.eliminated_hermitian]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyConjugacy: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyConjugacy: {ds.length} strict transitive checks passed"
