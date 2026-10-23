import Physics.StandardModel.Operators.Weinberg.LiWeinbergCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

example : Fintype.card (Sym (Fin 0) 2) = 0 ∧
    Fintype.card (Sym (Fin 1) 2) = 1 ∧ Fintype.card (Sym (Fin 3) 2) = 6 := by
  decide +kernel

example : Module.finrank ℂ (Physics.WeinbergSMInterface.ModelSector
    (Representation.trivial ℂ Unit (Fin 3 → ℂ))) = 6 := by
  rw [Physics.LiWeinbergCertificate.finite_trivial_finrank]

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "LLHH imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.LiWeinbergConvention.diagonal_local,
    ``Physics.LiWeinbergConvention.lepton_exchange, ``Physics.LiWeinbergConvention.higgs_exchange,
    ``Physics.LiWeinbergConvention.mixed_probe, ``Physics.LiWeinbergCertificate.ordered,
    ``Physics.LiWeinbergCertificate.candidate_eq, ``Physics.LiWeinbergCertificate.extract_candidate,
    ``Physics.LiWeinbergCertificate.candidate_extract, ``Physics.LiWeinbergCertificate.candidate_apply,
    ``Physics.LiWeinbergCertificate.candidate_diagonal, ``Physics.LiWeinbergCertificate.probe,
    ``Physics.LiWeinbergCertificate.mass_formula, ``Physics.LiWeinbergCertificate.finiteEquiv,
    ``Physics.LiWeinbergCertificate.flavorEquiv, ``Physics.LiWeinbergCertificate.flavor_finrank,
    ``Physics.LiWeinbergCertificate.finite_inverse_is_candidate,
    ``Physics.LiWeinbergCertificate.flavor_entry, ``Physics.LiWeinbergCertificate.flavorBasis_independent,
    ``Physics.LiWeinbergCertificate.flavorBasis_spans, ``Physics.LiWeinbergCertificate.flavorBasis_is_candidate,
    ``Physics.LiWeinbergCertificate.finite_trivial_finrank,
    ``Physics.LiWeinbergCertificate.sign_candidate_nonzero,
    ``Physics.LiWeinbergCertificate.onFields_extract, ``Physics.LiWeinbergCertificate.onFields_reconstruct]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "LLHH {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li LLHH: {ds.length} strict axiom checks passed"
