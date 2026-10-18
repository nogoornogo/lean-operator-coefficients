import Physics.StandardModel.Operators.SixQuarkTwoCoordinates
import Lean.Util.CollectAxioms

/-! Persisted strict transitive axiom checks for intrinsic two-coordinate completeness. -/
run_cmd do
  let declarations := [
    ``GUT.SixWeylMultilinear.pairing_invariant,
    ``GUT.SixQuarkInvariant.productPairing_invariant,
    ``GUT.SixQuarkInvariant.reconstruct_coordinates,
    ``GUT.SixQuarkInvariant.coordinates_reconstruct,
    ``GUT.SixQuarkSpeciesQuotient.color_permuted,
    ``GUT.SixQuarkSpeciesQuotient.spin_permuted,
    ``GUT.SixQuarkSpeciesQuotient.coordinates_statistics,
    ``GUT.SixQuarkSpeciesQuotient.embed_statistics,
    ``GUT.SixQuarkSpeciesQuotient.kernel_reconstruct,
    ``GUT.SixQuarkSpeciesQuotient.reconstruct_speciesAlternating,
    ``GUT.SixQuarkSpeciesQuotient.kernelEquiv,
    ``GUT.SixQuarkSpeciesQuotient.finrank_statisticsKernel,
    ``GUT.SixQuarkSpeciesQuotient.twoProbes_reconstruct_embed,
    ``GUT.SixQuarkSpeciesQuotient.probeEquiv,
    ``GUT.SixQuarkSpeciesQuotient.coefficientProbeEquiv,
    ``GUT.SixQuarkSpeciesQuotient.finrank_admissible,
    ``GUT.SixQuarkTwoCoordinates.orderedIntertwiner,
    ``GUT.SixQuarkTwoCoordinates.restriction_liftCoefficient,
    ``GUT.SixQuarkTwoCoordinates.liftCoefficient_restrictSector,
    ``GUT.SixQuarkTwoCoordinates.twoCoordinateEquiv,
    ``GUT.SixQuarkTwoCoordinates.finrank_sector,
    ``GUT.SixQuarkTwoCoordinates.probes_inverse,
    ``GUT.SixQuarkTwoCoordinates.inverse_probes]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two-coordinate completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two-coordinate completeness: {declarations.length} strict transitive axiom checks passed"
