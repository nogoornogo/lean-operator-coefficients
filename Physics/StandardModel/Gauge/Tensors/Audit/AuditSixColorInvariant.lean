import Physics.StandardModel.Gauge.Tensors.SixColorInvariant
import Lean.Util.CollectAxioms

/-! Strict transitive axiom checks for six-color invariant classification. -/

run_cmd do
  let declarations := [
    ``Physics.SixColorInvariant.basisValue_vanish,
    ``Physics.SixColorInvariant.basisValue_swap,
    ``Physics.SixColorInvariant.three_term,
    ``Physics.SixColorInvariant.eq_zero_of_probes,
    ``Physics.SixColorInvariant.pairing_invariant,
    ``Physics.SixColorInvariant.coordinates_reconstruct,
    ``Physics.SixColorInvariant.linearIndependent_pairing,
    ``Physics.SixColorInvariant.reconstruct_coordinates,
    ``Physics.SixColorInvariant.existsUnique_pairing_coordinates,
    ``Physics.SixColorInvariant.exists_pairing_coordinates,
    ``Physics.SixColorInvariant.eq_of_coordinates,
    ``Physics.SixColorInvariant.invariantEquiv,
    ``Physics.SixColorInvariant.basis_ext]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-color invariant classification: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-color invariant classification: {declarations.length} strict transitive axiom checks passed"
