import Physics.StandardModel.Operators.LiDuqlCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

example : Fintype.card ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) = 81 ∧
    Fintype.card ((Fin 1 × Fin 1) × (Fin 1 × Fin 1)) = 1 ∧
    Fintype.card ((Fin 0 × Fin 3) × (Fin 3 × Fin 3)) = 0 := by decide +kernel

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DUQL imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiDuqlConvention.fermionic_reorder,
    ``GUT.LiDuqlConvention.reorder_parity, ``GUT.LiDuqlCertificate.ordered_apply,
    ``GUT.LiDuqlCertificate.candidate_eq, ``GUT.LiDuqlCertificate.extract_candidate,
    ``GUT.LiDuqlCertificate.candidate_extract, ``GUT.LiDuqlCertificate.finiteEquiv,
    ``GUT.LiDuqlCertificate.flavorBasis, ``GUT.LiDuqlCertificate.flavor_finrank,
    ``GUT.LiDuqlCertificate.flavorBasis_independent,
    ``GUT.LiDuqlCertificate.flavorBasis_spans,
    ``GUT.LiDuqlCertificate.flavorBasis_is_candidate,
    ``GUT.LiDuqlCertificate.finite_inverse_is_candidate,
    ``Math.InvariantFunctionalCoordinates.equiv,
    ``Math.InvariantFunctionalCoordinates.unrestrictedEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DUQL {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li DUQL: {ds.length} strict axiom checks passed"
