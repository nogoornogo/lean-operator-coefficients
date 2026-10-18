import Physics.StandardModel.Gauge.SixColorInvariant
import Lean.Util.CollectAxioms

/-! Strict transitive axiom checks for six-color invariant classification. -/

run_cmd do
  let declarations := [
    ``GUT.SixColorInvariant.basisValue_vanish,
    ``GUT.SixColorInvariant.basisValue_swap,
    ``GUT.SixColorInvariant.three_term,
    ``GUT.SixColorInvariant.eq_zero_of_probes,
    ``GUT.SixColorInvariant.pairing_invariant,
    ``GUT.SixColorInvariant.coordinates_reconstruct,
    ``GUT.SixColorInvariant.linearIndependent_pairing,
    ``GUT.SixColorInvariant.reconstruct_coordinates,
    ``GUT.SixColorInvariant.existsUnique_pairing_coordinates,
    ``GUT.SixColorInvariant.exists_pairing_coordinates,
    ``GUT.SixColorInvariant.eq_of_coordinates,
    ``GUT.SixColorInvariant.invariantEquiv,
    ``GUT.SixColorInvariant.basis_ext]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-color invariant classification: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Six-color invariant classification: {declarations.length} strict transitive axiom checks passed"
