import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkResidual
import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFourFlavor
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Six-quark certificate imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.LiSixQuarkConvention.candidate_coordinates,
    ``Physics.LiSixQuarkConvention.candidate_invariant,
    ``Physics.LiSixQuarkConvention.extra_agrees,
    ``Physics.LiSixQuarkCertificate.left_inverse,
    ``Physics.LiSixQuarkCertificate.right_inverse,
    ``Physics.LiSixQuarkCertificate.extra_outside_printed_span,
    ``Physics.LiSixQuarkLocalBasis.orbit_independent,
    ``Physics.LiSixQuarkLocalBasis.literal_reconstruction,
    ``Physics.LiSixQuarkLocalBasis.local_finrank,
    ``Physics.LiSixQuarkResidual.statistics_iff,
    ``Physics.LiSixQuarkResidual.literal_local_assembly,
    ``Physics.LiSixQuarkResidual.physical_assembly_extraction,
    ``Physics.LiSixQuarkResidual.physical_extraction_assembly,
    ``Physics.LiSixQuarkResidual.onFields_reconstruction,
    ``Physics.LiSixQuarkResidual.scalar_finrank,
    ``Physics.LiSixQuarkResidual.scalar_physical_agrees,
    ``Physics.LiSixQuarkFourFlavor.separating_probe_witness,
    ``Physics.LiSixQuarkFourFlavor.physical_nonzero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Six-quark {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Li extended six-quark basis: {ds.length} strict axiom checks passed"
