# Spectrum-Only Exterior Qque Entry

## Statement

Keep the shared finite-dimensional source, strictly commuting G and H actions,
T-unitarity, symmetric T x H invariant mass B, two actual conjugations and a
continuous compatible SM-cover x H action D on its unchanged radical K.
H is compact, not necessarily finite or Abelian.

Supply n > 0, s natural, and an **SM-only equivariant linear equivalence**
between K and n complete left-chiral SM generations plus s singlets.
No residual generation representation, target or index equation is supplied.
H need not act trivially in this equivalence.

[ExactSMSpectrumQque](../../../Physics/StandardModel/Operators/ExactSMSpectrumQque.lean)
now proves `exists_actual_alternation` and `exists_actual_exterior` from these
inputs. Participating fields are actual subspaces of K and its dual. The
qque-originating coefficient has nonzero alternating descent with the retained
SM-cover x H x SL(2,C) invariance, as in the existing route B endpoint.

## Derived Interfaces

1. [Canonical residual targets](../../../Physics/StandardModel/Spectrum/ExactSMResidualSpectrum.lean)
   are Hom_SM(R,K), acted on by H through postcomposition. Gauge hypercharge
   separation gives Q/up/e multiplicity n and vanishing opposite species,
   hence the three species-index equations. Compact continuity supplies the
   analytic extraction inputs; Q is nontrivial since n > 0.
2. [Weight multiplicities](../../../Physics/StandardModel/Spectrum/ExactSMWeightMultiplicity.lean)
   follow by computing the exact SM character and using injectivity of the
   finite torus-character evaluator. All fifteen positive SM weights have
   dimension n; all opposite weights have dimension zero. Singlets contribute
   only at the trivial character. This step alone is not H-character equality.
3. [Evaluation](../../../Physics/StandardModel/Spectrum/ExactSMWeightEvaluation.lean)
   on [concrete nonzero gauge vectors](../../../Physics/StandardModel/Spectrum/MonitoredSMWeights.lean)
   maps each canonical multiplicity space into its actual torus sector.
   Compatibility with the physical covering torus proves the landing property;
   strict commutation proves H-equivariance. Gauge irreducibility gives
   injectivity, and the independently established dimensions give surjectivity.
4. [Four-weight target](../../../Physics/StandardModel/Spectrum/ExactSMFourWeightTarget.lean)
   follows from these H-equivariant isomorphisms and vanishing opposite sectors.
   `has_target` assumes no compactness, continuity, positive n or conjugations.
   Those retained hypotheses enter the final nonzero exterior theorem, not
   this spectrum comparison.

The vectors at slots 0/3 are color-weak basis tensors (0,0)/(1,1); slot 8
uses color-coordinate evaluation at 2 in upRight.dual, and slot 14 uses the
identity functional in electronRight.dual. Signs and inverse weights are
checked with the repository's integral 6Y convention.

## Boundaries

This theorem reduces the caller's representation-theoretic proof burden, not
the physical spectrum restriction: the whole light gauge spectrum is fixed.
It is narrower than the general index-based route, which may permit extra
fields. Equal total dimensions or equal generation counts alone do not imply
`HasSpectrum`. No virtual-index generalization or arbitrary vectorlike extension
is included. The intermediate `_of_four_weights` theorems remain available.

The result is an algebraic allowed coefficient, not a generated interaction,
nonzero decay amplitude or finite lifetime. No new ambient model satisfying
all source inputs is constructed here; the E6 literature boundary is unchanged.

## Verification

See the [topic record](README.md) for commands and final outcomes. Persistent
audits cover transitive axioms and layer boundaries, one and three generations,
singlets, opposite species/weights, zero-generation exclusion and dimension
15*n+s. These controls are not an ambient-GUT model-existence theorem.
