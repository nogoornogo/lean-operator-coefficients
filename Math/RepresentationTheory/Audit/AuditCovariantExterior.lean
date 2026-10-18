import Math.RepresentationTheory.AutomorphismCovariantExterior

open Lean in
run_cmd do
  let ds := [
    ``Math.AutomorphismCovariantExterior.exteriorAction,
    ``Math.AutomorphismCovariantExterior.ofGenerators,
    ``Math.AutomorphismCovariantExterior.supportedAction,
    ``Math.AutomorphismCovariantExterior.supportEquiv,
    ``Math.AutomorphismCovariantExterior.equiv,
    ``Math.AutomorphismCovariantExterior.forbidden_iff,
    ``Math.AutomorphismCovariantExterior.inputEquiv,
    ``Math.AutomorphismCovariantExterior.input_forbidden_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Covariant exterior {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Covariant exterior: {ds.length} strict transitive checks passed"
