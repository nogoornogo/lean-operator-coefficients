import Physics.StandardModel.Operators.BaryonOne.Qque.StandardGaugeQqueExterior
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``Physics.StandardGaugeQqueExterior.standard_nonzero,
    ``Physics.StandardGaugeQqueExterior.on_fields]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Standard gauge exterior: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Standard gauge exterior: {ds.length} strict transitive checks passed"
