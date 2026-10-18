import Physics.StandardModel.Operators.LiWeinbergCertificate
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

example : Fintype.card (Sym (Fin 0) 2) = 0 ∧
    Fintype.card (Sym (Fin 1) 2) = 1 ∧ Fintype.card (Sym (Fin 3) 2) = 6 := by
  decide +kernel

example : Module.finrank ℂ (GUT.WeinbergSMInterface.ModelSector
    (Representation.trivial ℂ Unit (Fin 3 → ℂ))) = 6 := by
  rw [GUT.LiWeinbergCertificate.finite_trivial_finrank]

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "LLHH imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiWeinbergConvention.diagonal_local,
    ``GUT.LiWeinbergConvention.lepton_exchange, ``GUT.LiWeinbergConvention.higgs_exchange,
    ``GUT.LiWeinbergConvention.mixed_probe, ``GUT.LiWeinbergCertificate.ordered,
    ``GUT.LiWeinbergCertificate.candidate_eq, ``GUT.LiWeinbergCertificate.extract_candidate,
    ``GUT.LiWeinbergCertificate.candidate_extract, ``GUT.LiWeinbergCertificate.candidate_apply,
    ``GUT.LiWeinbergCertificate.candidate_diagonal, ``GUT.LiWeinbergCertificate.probe,
    ``GUT.LiWeinbergCertificate.mass_formula, ``GUT.LiWeinbergCertificate.finiteEquiv,
    ``GUT.LiWeinbergCertificate.flavorEquiv, ``GUT.LiWeinbergCertificate.flavor_finrank,
    ``GUT.LiWeinbergCertificate.finite_inverse_is_candidate,
    ``GUT.LiWeinbergCertificate.flavor_entry, ``GUT.LiWeinbergCertificate.flavorBasis_independent,
    ``GUT.LiWeinbergCertificate.flavorBasis_spans, ``GUT.LiWeinbergCertificate.flavorBasis_is_candidate,
    ``GUT.LiWeinbergCertificate.finite_trivial_finrank,
    ``GUT.LiWeinbergCertificate.sign_candidate_nonzero,
    ``GUT.LiWeinbergCertificate.onFields_extract, ``GUT.LiWeinbergCertificate.onFields_reconstruct]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "LLHH {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li LLHH: {ds.length} strict axiom checks passed"
