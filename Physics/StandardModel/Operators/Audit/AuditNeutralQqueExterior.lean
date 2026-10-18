import Physics.StandardModel.Operators.NeutralQqueExterior
open Lean in
run_cmd do
  let ds := [``GUT.NeutralQqueExterior.charged_apply,
    ``GUT.NeutralQqueExterior.charged_dual, ``GUT.NeutralQqueExterior.chargedEquiv,
    ``GUT.NeutralQqueExterior.coefficient_witness,
    ``GUT.NeutralQqueExterior.coefficient_nonzero,
    ``GUT.NeutralQqueExterior.has_nonzero_alternation,
    ``GUT.NeutralQqueExterior.neutral_of_pointwise_block,
    ``GUT.NeutralQqueExterior.exists_of_pointwise_block,
    ``GUT.NeutralQqueExterior.exists_on_fields]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Neutral qque exterior {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Neutral qque exterior: {ds.length} strict transitive checks passed"
