# LLHH rank certificate

## Fixed input and proved result

The input is the constant signed-species word `(3,3)` (two left-handed
leptons), three complex flavors, Higgs constituent `m=2`, `delta=2`.
It is the derivative-free LLHH sector with one Higgs species. The conjugate
sector is not added to its complex coefficient count.

[LLHHKernelRank](../../../Physics/StandardModel/Operators/LLHHKernelRank.lean)
proves, for the actual `SMFullLocalKernel` matrix with trivial residual group:

- `carrier_dimension`: 198 columns (`choose(12,2) * 3`).
- `kernel_dimension`: six independent complex coefficients.
- `rank`: rank 192.
- `explicit_rank` and `rank_preserved`: the same rank after replacing the
  classical basis with the explicitly indexed exterior/tensor basis.

There are 21 local group tests (`9+4*(2+1)`), hence the original stacked
constraint matrix has 4158 rows and 198 columns. The proof does not evaluate
those entries numerically: it derives the exact rank from the kernel and
carrier dimensions. No approximate elimination or supplied rank is used.

## Constructed interfaces

[ConstantPatternExterior](../../../Math/RepresentationTheory/ConstantPatternExterior.lean)
identifies a constant-species statistical source with the exterior power of
that species. Its forward map is species injection followed by the existing
content projection; its inverse is the exterior power of species evaluation.
Both inverse identities and equivariance are proved for arbitrary species,
degree and supplied representation. There is no dimension assumption.

For LLHH, `sourceEquiv` and `bosonEquiv` construct the field/Higgs connection;
`coefficientEquiv` reaches the existing Weinberg coefficient space.
`coordinates` and `kernelCoordinates` identify coefficients and the actual
kernel with `Sym (Fin 3) 2 → ℂ`. The six indices are unordered flavor pairs.
`reconstruct_extract` and `extract_reconstruct` certify both directions.
`coefficientBasis` is their transported coordinate basis.

`leptonBasis` uses weak, Weyl and flavor standard bases reindexed by `Fin 12`.
`carrierBasis` uses two-element exterior indices and degree-two symmetric
Higgs indices, transported through `fullEquiv`. It does not choose an
unspecified basis with `Module.finBasis`. The declarations are nevertheless
in a `noncomputable` section: arbitrary complex scalars and the existing
abstract quotients are not an executable exact-arithmetic backend. Explicit
finite coordinates and a kernel-checked rank certificate are the achievement.

`residualEquiv` separately proves the actual full-group coefficient space
is isomorphic to `Hom_H(Sym²(flavor 3), C)` for any residual group and the
supplied three-flavor representations on all ten species. Only the lepton
flavor enters the output. This is not a claim that imposing an arbitrary
residual action leaves six invariants. The rank-192 theorem concerns local
constraints before residual invariance.

## Reuse and boundaries

The epsilon-contraction classification, symmetric flavor reconstruction and
dimension formula were already proved in `WeinbergSMInterface` and
`LiWeinbergCertificate`. The new result joins these to the generic statistical
source and original finite kernel. The literature in [the reference record](literature.md)
is methodological guidance, not a premise of these proofs.

This completes the agreed fixed LLHH endpoint. General content compression,
numerical ranks of all neutral contents and all-degree reclassification of
the 572 assignments remain outside this result. No new coaction or general
algebraic-group foundation was needed. No claim about generated interactions,
neutrino masses, amplitudes or rates is inferred from coefficient allowance.
