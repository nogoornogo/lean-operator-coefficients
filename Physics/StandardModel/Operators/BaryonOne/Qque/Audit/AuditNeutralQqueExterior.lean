import Physics.StandardModel.Operators.BaryonOne.Qque.NeutralQqueExterior
open Lean in
run_cmd do
  let ds := [``Physics.NeutralQqueExterior.charged_apply,
    ``Physics.NeutralQqueExterior.charged_dual, ``Physics.NeutralQqueExterior.chargedEquiv,
    ``Physics.NeutralQqueExterior.coefficient_witness,
    ``Physics.NeutralQqueExterior.coefficient_nonzero,
    ``Physics.NeutralQqueExterior.has_nonzero_alternation,
    ``Physics.NeutralQqueExterior.neutral_of_pointwise_block,
    ``Physics.NeutralQqueExterior.exists_of_pointwise_block,
    ``Physics.NeutralQqueExterior.exists_on_fields]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Neutral qque exterior {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Neutral qque exterior: {ds.length} strict transitive checks passed"
