import Physics.StandardModel.Operators.Selection.QLFiniteSupport
import Lean.Util.CollectAxioms

run_cmd do
  let ds := [``Physics.QLFiniteSupport.character_product,
    ``Physics.QLFiniteSupport.raw_residual,
    ``Physics.QLFiniteSupport.source_residual,
    ``Physics.QLFiniteSupport.boson_residual,
    ``Physics.QLFiniteSupport.action_residual,
    ``Physics.QLFiniteSupport.test_allowed_iff,
    ``Physics.QLFiniteSupport.field_local,
    ``Physics.QLFiniteSupport.original_allowed_iff,
    ``Physics.QLFiniteSupport.family_charge_controls]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "q/l finite support: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"q/l finite support: {ds.length} strict transitive axiom checks passed"
