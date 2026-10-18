import Physics.StandardModel.Operators.LiDuueCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

example : Fintype.card ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) = 81 ∧
    Fintype.card ((Fin 1 × Fin 1) × (Fin 1 × Fin 1)) = 1 ∧
    Fintype.card ((Fin 3 × Fin 3) × (Fin 0 × Fin 3)) = 0 := by decide +kernel

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DUUE imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiDuueConvention.reorder_symmetric,
    ``GUT.LiDuueConvention.conjugate_symmetric,
    ``GUT.LiDuueConvention.conjugate_alternating,
    ``GUT.LiDuueConvention.reorder_alternating,
    ``GUT.LiDuueConvention.local_reconstruction,
    ``GUT.LiDuueConvention.source_symmetries, ``GUT.LiDuueCertificate.ordered_apply,
    ``GUT.LiDuueCertificate.restriction_candidate, ``GUT.LiDuueCertificate.candidate_eq,
    ``GUT.LiDuueCertificate.extract_candidate, ``GUT.LiDuueCertificate.candidate_extract,
    ``GUT.LiDuueCertificate.finiteEquiv, ``GUT.LiDuueCertificate.flavorBasis,
    ``GUT.LiDuueCertificate.flavor_finrank, ``GUT.LiDuueCertificate.finite_inverse_is_candidate,
    ``GUT.LiDuueCertificate.flavorBasis_independent,
    ``GUT.LiDuueCertificate.flavorBasis_spans,
    ``GUT.LiDuueCertificate.flavorBasis_is_candidate]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DUUE {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li DUUE: {ds.length} strict axiom checks passed"
