import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuqlCertificate
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
  let ds := [``Physics.LiDuqlConvention.fermionic_reorder,
    ``Physics.LiDuqlConvention.reorder_parity, ``Physics.LiDuqlCertificate.ordered_apply,
    ``Physics.LiDuqlCertificate.candidate_eq, ``Physics.LiDuqlCertificate.extract_candidate,
    ``Physics.LiDuqlCertificate.candidate_extract, ``Physics.LiDuqlCertificate.finiteEquiv,
    ``Physics.LiDuqlCertificate.flavorBasis, ``Physics.LiDuqlCertificate.flavor_finrank,
    ``Physics.LiDuqlCertificate.flavorBasis_independent,
    ``Physics.LiDuqlCertificate.flavorBasis_spans,
    ``Physics.LiDuqlCertificate.flavorBasis_is_candidate,
    ``Physics.LiDuqlCertificate.finite_inverse_is_candidate,
    ``Math.InvariantFunctionalCoordinates.equiv,
    ``Math.InvariantFunctionalCoordinates.unrestrictedEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DUQL {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li DUQL: {ds.length} strict axiom checks passed"
