import Physics.StandardModel.Operators.DevMohapatraHeavyConjugacy
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyConjugacy imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraHeavyConjugacy.adj,
    ``GUT.DevMohapatraHeavyConjugacy.field_involutive,
    ``GUT.DevMohapatraHeavyConjugacy.adj_involutive,
    ``GUT.DevMohapatraHeavyConjugacy.adj_mul,
    ``GUT.DevMohapatraHeavyConjugacy.adj_smul,
    ``GUT.DevMohapatraHeavyConjugacy.adj_add,
    ``GUT.DevMohapatraHeavyConjugacy.adj_sub,
    ``GUT.DevMohapatraHeavyConjugacy.adj_neg,
    ``GUT.DevMohapatraHeavyConjugacy.adj_zero,
    ``GUT.DevMohapatraHeavyConjugacy.include_adj,
    ``GUT.DevMohapatraHeavyConjugacy.include_injective,
    ``GUT.DevMohapatraHeavyConjugacy.adj_current,
    ``GUT.DevMohapatraHeavyConjugacy.adj_bar_current,
    ``GUT.DevMohapatraHeavyConjugacy.field_bar_u,
    ``GUT.DevMohapatraHeavyConjugacy.adj_cross,
    ``GUT.DevMohapatraHeavyConjugacy.conjugated,
    ``GUT.DevMohapatraHeavyConjugacy.residual_conjugated,
    ``GUT.DevMohapatraHeavyConjugacy.solution_conjugated,
    ``GUT.DevMohapatraHeavyConjugacy.solution_adjoint,
    ``GUT.DevMohapatraHeavyConjugacy.adj_generator,
    ``GUT.DevMohapatraHeavyConjugacy.adj_sum,
    ``GUT.DevMohapatraHeavyConjugacy.evaluate_conjugate_generator,
    ``GUT.DevMohapatraHeavyConjugacy.evaluate_hc,
    ``GUT.DevMohapatraHeavyConjugacy.eliminated_hermitian]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyConjugacy: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyConjugacy: {ds.length} strict transitive checks passed"
