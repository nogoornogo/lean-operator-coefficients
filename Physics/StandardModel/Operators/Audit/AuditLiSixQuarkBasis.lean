import Physics.StandardModel.Operators.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.LiSixQuarkResidual
import Physics.StandardModel.Operators.LiSixQuarkFourFlavor
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Six-quark certificate imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.LiSixQuarkConvention.candidate_coordinates,
    ``GUT.LiSixQuarkConvention.candidate_invariant,
    ``GUT.LiSixQuarkConvention.extra_agrees,
    ``GUT.LiSixQuarkCertificate.left_inverse,
    ``GUT.LiSixQuarkCertificate.right_inverse,
    ``GUT.LiSixQuarkCertificate.extra_outside_printed_span,
    ``GUT.LiSixQuarkLocalBasis.orbit_independent,
    ``GUT.LiSixQuarkLocalBasis.literal_reconstruction,
    ``GUT.LiSixQuarkLocalBasis.local_finrank,
    ``GUT.LiSixQuarkResidual.statistics_iff,
    ``GUT.LiSixQuarkResidual.literal_local_assembly,
    ``GUT.LiSixQuarkResidual.physical_assembly_extraction,
    ``GUT.LiSixQuarkResidual.physical_extraction_assembly,
    ``GUT.LiSixQuarkResidual.onFields_reconstruction,
    ``GUT.LiSixQuarkResidual.scalar_finrank,
    ``GUT.LiSixQuarkResidual.scalar_physical_agrees,
    ``GUT.LiSixQuarkFourFlavor.separating_probe_witness,
    ``GUT.LiSixQuarkFourFlavor.physical_nonzero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-quark {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li extended six-quark basis: {ds.length} strict axiom checks passed"
