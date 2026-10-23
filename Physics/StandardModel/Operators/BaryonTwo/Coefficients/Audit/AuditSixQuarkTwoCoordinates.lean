import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTwoCoordinates
import Lean.Util.CollectAxioms

/-! Persisted strict transitive axiom checks for intrinsic two-coordinate completeness. -/
run_cmd do
  let declarations := [
    ``Physics.SixWeylMultilinear.pairing_invariant,
    ``Physics.SixQuarkInvariant.productPairing_invariant,
    ``Physics.SixQuarkInvariant.reconstruct_coordinates,
    ``Physics.SixQuarkInvariant.coordinates_reconstruct,
    ``Physics.SixQuarkSpeciesQuotient.color_permuted,
    ``Physics.SixQuarkSpeciesQuotient.spin_permuted,
    ``Physics.SixQuarkSpeciesQuotient.coordinates_statistics,
    ``Physics.SixQuarkSpeciesQuotient.embed_statistics,
    ``Physics.SixQuarkSpeciesQuotient.kernel_reconstruct,
    ``Physics.SixQuarkSpeciesQuotient.reconstruct_speciesAlternating,
    ``Physics.SixQuarkSpeciesQuotient.kernelEquiv,
    ``Physics.SixQuarkSpeciesQuotient.finrank_statisticsKernel,
    ``Physics.SixQuarkSpeciesQuotient.twoProbes_reconstruct_embed,
    ``Physics.SixQuarkSpeciesQuotient.probeEquiv,
    ``Physics.SixQuarkSpeciesQuotient.coefficientProbeEquiv,
    ``Physics.SixQuarkSpeciesQuotient.finrank_admissible,
    ``Physics.SixQuarkTwoCoordinates.orderedIntertwiner,
    ``Physics.SixQuarkTwoCoordinates.restriction_liftCoefficient,
    ``Physics.SixQuarkTwoCoordinates.liftCoefficient_restrictSector,
    ``Physics.SixQuarkTwoCoordinates.twoCoordinateEquiv,
    ``Physics.SixQuarkTwoCoordinates.finrank_sector,
    ``Physics.SixQuarkTwoCoordinates.probes_inverse,
    ``Physics.SixQuarkTwoCoordinates.inverse_probes]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two-coordinate completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two-coordinate completeness: {declarations.length} strict transitive axiom checks passed"
