import Physics.StandardModel.Operators.QLFiniteSupport
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``GUT.QLFiniteSupport.character_product,
    ``GUT.QLFiniteSupport.raw_residual,
    ``GUT.QLFiniteSupport.source_residual,
    ``GUT.QLFiniteSupport.boson_residual,
    ``GUT.QLFiniteSupport.action_residual,
    ``GUT.QLFiniteSupport.test_allowed_iff,
    ``GUT.QLFiniteSupport.field_local,
    ``GUT.QLFiniteSupport.original_allowed_iff,
    ``GUT.QLFiniteSupport.family_charge_controls]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "q/l finite support: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"q/l finite support: {ds.length} strict transitive axiom checks passed"
