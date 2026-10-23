import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkSpeciesQuotient
import Physics.StandardModel.Operators.SixQuarkInvariant
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkSpeciesQuotient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkSpeciesQuotient.SatisfiesStatistics => Physics.SixQuarkSpeciesQuotient.SatisfiesStatistics,
  GUT.SixQuarkSpeciesQuotient.admissible => Physics.SixQuarkSpeciesQuotient.admissible,
  GUT.SixQuarkSpeciesQuotient.coefficientProbeEquiv => Physics.SixQuarkSpeciesQuotient.coefficientProbeEquiv,
  GUT.SixQuarkSpeciesQuotient.colorMatrix => Physics.SixQuarkSpeciesQuotient.colorMatrix,
  GUT.SixQuarkSpeciesQuotient.colorMatrix.eq_1 => Physics.SixQuarkSpeciesQuotient.colorMatrix.eq_1,
  GUT.SixQuarkSpeciesQuotient.color_permuted => Physics.SixQuarkSpeciesQuotient.color_permuted,
  GUT.SixQuarkSpeciesQuotient.coordinates_statistics => Physics.SixQuarkSpeciesQuotient.coordinates_statistics,
  GUT.SixQuarkSpeciesQuotient.embed => Physics.SixQuarkSpeciesQuotient.embed,
  GUT.SixQuarkSpeciesQuotient.embed.eq_1 => Physics.SixQuarkSpeciesQuotient.embed.eq_1,
  GUT.SixQuarkSpeciesQuotient.embed_statistics => Physics.SixQuarkSpeciesQuotient.embed_statistics,
  GUT.SixQuarkSpeciesQuotient.eq_of_twoProbes => Physics.SixQuarkSpeciesQuotient.eq_of_twoProbes,
  GUT.SixQuarkSpeciesQuotient.finrank_admissible => Physics.SixQuarkSpeciesQuotient.finrank_admissible,
  GUT.SixQuarkSpeciesQuotient.finrank_statisticsKernel => Physics.SixQuarkSpeciesQuotient.finrank_statisticsKernel,
  GUT.SixQuarkSpeciesQuotient.fromProbes => Physics.SixQuarkSpeciesQuotient.fromProbes,
  GUT.SixQuarkSpeciesQuotient.fromProbes.eq_1 => Physics.SixQuarkSpeciesQuotient.fromProbes.eq_1,
  GUT.SixQuarkSpeciesQuotient.fromProbesCoefficient => Physics.SixQuarkSpeciesQuotient.fromProbesCoefficient,
  GUT.SixQuarkSpeciesQuotient.fromProbes_probes => Physics.SixQuarkSpeciesQuotient.fromProbes_probes,
  GUT.SixQuarkSpeciesQuotient.generators_species_sign => Physics.SixQuarkSpeciesQuotient.generators_species_sign,
  GUT.SixQuarkSpeciesQuotient.kernelEquiv => Physics.SixQuarkSpeciesQuotient.kernelEquiv,
  GUT.SixQuarkSpeciesQuotient.kernel_reconstruct => Physics.SixQuarkSpeciesQuotient.kernel_reconstruct,
  GUT.SixQuarkSpeciesQuotient.probeEquiv => Physics.SixQuarkSpeciesQuotient.probeEquiv,
  GUT.SixQuarkSpeciesQuotient.probeEquiv_apply => Physics.SixQuarkSpeciesQuotient.probeEquiv_apply,
  GUT.SixQuarkSpeciesQuotient.probes_fromProbes => Physics.SixQuarkSpeciesQuotient.probes_fromProbes,
  GUT.SixQuarkSpeciesQuotient.reconstruct_fromProbes => Physics.SixQuarkSpeciesQuotient.reconstruct_fromProbes,
  GUT.SixQuarkSpeciesQuotient.reconstruct_speciesAlternating => Physics.SixQuarkSpeciesQuotient.reconstruct_speciesAlternating,
  GUT.SixQuarkSpeciesQuotient.reconstruct_transform => Physics.SixQuarkSpeciesQuotient.reconstruct_transform,
  GUT.SixQuarkSpeciesQuotient.residual => Physics.SixQuarkSpeciesQuotient.residual,
  GUT.SixQuarkSpeciesQuotient.residual.eq_1 => Physics.SixQuarkSpeciesQuotient.residual.eq_1,
  GUT.SixQuarkSpeciesQuotient.slotSwap => Physics.SixQuarkSpeciesQuotient.slotSwap,
  GUT.SixQuarkSpeciesQuotient.slotSwap.eq_1 => Physics.SixQuarkSpeciesQuotient.slotSwap.eq_1,
  GUT.SixQuarkSpeciesQuotient.spinMatrix => Physics.SixQuarkSpeciesQuotient.spinMatrix,
  GUT.SixQuarkSpeciesQuotient.spinMatrix.eq_1 => Physics.SixQuarkSpeciesQuotient.spinMatrix.eq_1,
  GUT.SixQuarkSpeciesQuotient.spin_permuted => Physics.SixQuarkSpeciesQuotient.spin_permuted,
  GUT.SixQuarkSpeciesQuotient.statisticsKernel => Physics.SixQuarkSpeciesQuotient.statisticsKernel,
  GUT.SixQuarkSpeciesQuotient.transform => Physics.SixQuarkSpeciesQuotient.transform,
  GUT.SixQuarkSpeciesQuotient.transform.eq_1 => Physics.SixQuarkSpeciesQuotient.transform.eq_1,
  GUT.SixQuarkSpeciesQuotient.twoProbes => Physics.SixQuarkSpeciesQuotient.twoProbes,
  GUT.SixQuarkSpeciesQuotient.twoProbes_reconstruct_embed => Physics.SixQuarkSpeciesQuotient.twoProbes_reconstruct_embed
]

assert_compatible GUT.SixQuarkSpeciesQuotient.SatisfiesStatistics => Physics.SixQuarkSpeciesQuotient.SatisfiesStatistics
assert_compatible GUT.SixQuarkSpeciesQuotient.admissible => Physics.SixQuarkSpeciesQuotient.admissible
assert_compatible GUT.SixQuarkSpeciesQuotient.coefficientProbeEquiv => Physics.SixQuarkSpeciesQuotient.coefficientProbeEquiv
assert_compatible GUT.SixQuarkSpeciesQuotient.colorMatrix => Physics.SixQuarkSpeciesQuotient.colorMatrix
assert_compatible GUT.SixQuarkSpeciesQuotient.colorMatrix.eq_1 => Physics.SixQuarkSpeciesQuotient.colorMatrix.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.color_permuted => Physics.SixQuarkSpeciesQuotient.color_permuted
assert_compatible GUT.SixQuarkSpeciesQuotient.coordinates_statistics => Physics.SixQuarkSpeciesQuotient.coordinates_statistics
assert_compatible GUT.SixQuarkSpeciesQuotient.embed => Physics.SixQuarkSpeciesQuotient.embed
assert_compatible GUT.SixQuarkSpeciesQuotient.embed.eq_1 => Physics.SixQuarkSpeciesQuotient.embed.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.embed_statistics => Physics.SixQuarkSpeciesQuotient.embed_statistics
assert_compatible GUT.SixQuarkSpeciesQuotient.eq_of_twoProbes => Physics.SixQuarkSpeciesQuotient.eq_of_twoProbes
assert_compatible GUT.SixQuarkSpeciesQuotient.finrank_admissible => Physics.SixQuarkSpeciesQuotient.finrank_admissible
assert_compatible GUT.SixQuarkSpeciesQuotient.finrank_statisticsKernel => Physics.SixQuarkSpeciesQuotient.finrank_statisticsKernel
assert_compatible GUT.SixQuarkSpeciesQuotient.fromProbes => Physics.SixQuarkSpeciesQuotient.fromProbes
assert_compatible GUT.SixQuarkSpeciesQuotient.fromProbes.eq_1 => Physics.SixQuarkSpeciesQuotient.fromProbes.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.fromProbesCoefficient => Physics.SixQuarkSpeciesQuotient.fromProbesCoefficient
assert_compatible GUT.SixQuarkSpeciesQuotient.fromProbes_probes => Physics.SixQuarkSpeciesQuotient.fromProbes_probes
assert_compatible GUT.SixQuarkSpeciesQuotient.generators_species_sign => Physics.SixQuarkSpeciesQuotient.generators_species_sign
assert_compatible GUT.SixQuarkSpeciesQuotient.kernelEquiv => Physics.SixQuarkSpeciesQuotient.kernelEquiv
assert_compatible GUT.SixQuarkSpeciesQuotient.kernel_reconstruct => Physics.SixQuarkSpeciesQuotient.kernel_reconstruct
assert_compatible GUT.SixQuarkSpeciesQuotient.probeEquiv => Physics.SixQuarkSpeciesQuotient.probeEquiv
assert_compatible GUT.SixQuarkSpeciesQuotient.probeEquiv_apply => Physics.SixQuarkSpeciesQuotient.probeEquiv_apply
assert_compatible GUT.SixQuarkSpeciesQuotient.probes_fromProbes => Physics.SixQuarkSpeciesQuotient.probes_fromProbes
assert_compatible GUT.SixQuarkSpeciesQuotient.reconstruct_fromProbes => Physics.SixQuarkSpeciesQuotient.reconstruct_fromProbes
assert_compatible GUT.SixQuarkSpeciesQuotient.reconstruct_speciesAlternating => Physics.SixQuarkSpeciesQuotient.reconstruct_speciesAlternating
assert_compatible GUT.SixQuarkSpeciesQuotient.reconstruct_transform => Physics.SixQuarkSpeciesQuotient.reconstruct_transform
assert_compatible GUT.SixQuarkSpeciesQuotient.residual => Physics.SixQuarkSpeciesQuotient.residual
assert_compatible GUT.SixQuarkSpeciesQuotient.residual.eq_1 => Physics.SixQuarkSpeciesQuotient.residual.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.slotSwap => Physics.SixQuarkSpeciesQuotient.slotSwap
assert_compatible GUT.SixQuarkSpeciesQuotient.slotSwap.eq_1 => Physics.SixQuarkSpeciesQuotient.slotSwap.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.spinMatrix => Physics.SixQuarkSpeciesQuotient.spinMatrix
assert_compatible GUT.SixQuarkSpeciesQuotient.spinMatrix.eq_1 => Physics.SixQuarkSpeciesQuotient.spinMatrix.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.spin_permuted => Physics.SixQuarkSpeciesQuotient.spin_permuted
assert_compatible GUT.SixQuarkSpeciesQuotient.statisticsKernel => Physics.SixQuarkSpeciesQuotient.statisticsKernel
assert_compatible GUT.SixQuarkSpeciesQuotient.transform => Physics.SixQuarkSpeciesQuotient.transform
assert_compatible GUT.SixQuarkSpeciesQuotient.transform.eq_1 => Physics.SixQuarkSpeciesQuotient.transform.eq_1
assert_compatible GUT.SixQuarkSpeciesQuotient.twoProbes => Physics.SixQuarkSpeciesQuotient.twoProbes
assert_compatible GUT.SixQuarkSpeciesQuotient.twoProbes_reconstruct_embed => Physics.SixQuarkSpeciesQuotient.twoProbes_reconstruct_embed
