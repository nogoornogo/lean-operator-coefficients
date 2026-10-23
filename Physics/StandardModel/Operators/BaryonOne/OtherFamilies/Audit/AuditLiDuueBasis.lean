import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.LiDuueCertificate
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
  let ds := [``Physics.LiDuueConvention.reorder_symmetric,
    ``Physics.LiDuueConvention.conjugate_symmetric,
    ``Physics.LiDuueConvention.conjugate_alternating,
    ``Physics.LiDuueConvention.reorder_alternating,
    ``Physics.LiDuueConvention.local_reconstruction,
    ``Physics.LiDuueConvention.source_symmetries, ``Physics.LiDuueCertificate.ordered_apply,
    ``Physics.LiDuueCertificate.restriction_candidate, ``Physics.LiDuueCertificate.candidate_eq,
    ``Physics.LiDuueCertificate.extract_candidate, ``Physics.LiDuueCertificate.candidate_extract,
    ``Physics.LiDuueCertificate.finiteEquiv, ``Physics.LiDuueCertificate.flavorBasis,
    ``Physics.LiDuueCertificate.flavor_finrank, ``Physics.LiDuueCertificate.finite_inverse_is_candidate,
    ``Physics.LiDuueCertificate.flavorBasis_independent,
    ``Physics.LiDuueCertificate.flavorBasis_spans,
    ``Physics.LiDuueCertificate.flavorBasis_is_candidate]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DUUE {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li DUUE: {ds.length} strict axiom checks passed"
