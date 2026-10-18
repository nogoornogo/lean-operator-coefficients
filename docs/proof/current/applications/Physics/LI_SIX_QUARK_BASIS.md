# Extended Li Six-Quark Local Basis Certificate

## Result And Scope

The specified derivative-free six-right-quark `(2,4)` sector is compared with
the ten Young-projected seeds printed in Li et al. These are extended by an
explicit alternating-down / symmetric-up seed. Twenty-five selected orbit
contractions give coordinates on the independent local invariant space.
This is an extension of the printed list, not a claim to have verified the
entire paper or every dimension-nine SMEFT sector.

Sources: [literal conventions](../../../../../Physics/StandardModel/Operators/LiSixQuarkConvention.lean),
[local basis](../../../../../Physics/StandardModel/Operators/LiSixQuarkLocalBasis.lean),
[residual interface](../../../../../Physics/StandardModel/Operators/LiSixQuarkResidual.lean),
[four-flavor witness](../../../../../Physics/StandardModel/Operators/LiSixQuarkFourFlavor.lean),
[audit](../../../../../Physics/StandardModel/Operators/Audit/AuditLiSixQuarkBasis.lean).

## Reading the structural derivation

The [source-to-block derivation](../../../../topics/proof-readability-review/source-derivation.md)
starts from polynomial epsilon identities and transports the factored Young
actions to actual multilinear coefficients. A uniform identity on arbitrary
six-slot functions checks the literal 48-term convention. The projected seeds
are constructed by this recipe; no cached 275-component seed table is assumed.

Explicit color and spin coordinate changes split local arrays into
4-, 6-, 6- and 9-dimensional invariant blocks. The Young images have named
directions with nineteen scalar source amplitudes. Selected exchange words
construct the forward columns. Symbolic block solvers supply extraction and a
left inverse; the general finite-square-matrix theorem supplies the right
inverse. Neither a proposed dense inverse nor an independently stored forward
matrix is a proof premise.

The normalized probe $P$ and extra vector $e$ satisfy $P(e)=1$. Every local
array has the unique split $c=(c-P(c)e)+P(c)e$. The
[independent probe decomposition](../../../../../Physics/StandardModel/Operators/LiSixQuarkProbeDecomposition.lean)
proves this and $\dim\ker P=24$. The printed Young images have zero trace in
the first product block, which is precisely the vanishing probe condition.
The selected-orbit basis and the unchanged printed-span argument then identify
the printed span with this kernel. Small source-index, scalar and polynomial
checks remain; no claim that finite arithmetic has disappeared is intended.

## Inputs And Citation Role

[Li et al., arXiv:2007.07899v1, equation (5.63), page 46](https://arxiv.org/pdf/2007.07899v1#page=46)
supplies the first ten contractions and tableau choices, not a trusted
completeness premise. The [source dictionary](../../../../topics/li-six-quark-basis/source-recovery.md)
records the epsilon interpretation, signs, ordering and normalization.
The generic EFT paper motivates the method but is not the source of these data.

The local space uses the existing defining color and Weyl representations.
General physical transport allows arbitrary complex up/down carriers, following
the [basis-free inverse extension](GRADED_SIX_QUARK_COMPARISON.md), with their separate representations of an arbitrary residual
group, and the typed slot family `(U,D,U,D,D,D)`. Actual fields require the
existing supplied equivariant `Inputs`. Compactness, a common up/down carrier,
and a three-generation restriction are not added.

## Certificate And Assembly

The literal candidates are finite sums of permuted epsilon contractions,
defined independently of extraction. Their coordinate agreement follows from
the raw epsilon reconstructions, linear generator transport and the Young
factorization. Rational-to-complex transport is proved for the recipe and
exchange words. The forward matrix is a presentation of these constructed
orbits; its extraction map is derived by block reconstruction. The old inverse,
seed-coordinate cache and separate stepping certificate have been retired.
The external Python script is diagnostic evidence, not a proof premise.

`orbit_independent` and `literal_reconstruction` identify the selected literal
contractions as a basis of the independently defined invariant submodule.
`extra_outside_printed_span` separates the additional component from the span
of every within-species exchange word applied to the ten printed seeds.
This separation is independent of the Python rank calculation.

## Residual And Physical Consumers

`statistics_iff` states the four transported exchange equations explicitly.
`physicalEquiv` and its inverse identities classify the existing physical
exterior sector by the constrained orbit Hom. `onFieldsEquiv` transports this
classification through supplied actual-field identifications. These maps reuse
the established normalized exterior descent rather than redefining the sector
as the image of the candidates. The 25 entries are not free flavor coefficients.

The scalar specialization agrees with the established two-probe equivalence
and has dimension two. The extra local line fails scalar statistics; it is not
a third one-generation operator. A determinant flavor tensor with `U = C`,
`D = C^4`, and trivial residual symmetry restores the required alternation
and gives a nonzero physical coefficient for the added component.

## Boundaries And Verification

No complete eleven-factor Schur-functor decomposition, general flavor counting,
or paper-wide error claim is made. In particular, a fourth alternating down
flavor is invisible in the one- and three-generation restrictions. Four-component
charge-conjugation conventions are not inferred from the epsilon dictionary.
Other chiralities, derivatives, EOM/IBP, amplitudes, UV matching and rates are
outside this certificate. Verification and completion status belong to the
[original topic record](../../../../topics/li-six-quark-basis/README.md) and
[structural replacement topic](../../../../topics/proof-readability-review/README.md).

## Earlier six-fermion literature

[Rao–Shrock, *Six-fermion (B−L)-violating operators of arbitrary generational structure*](https://doi.org/10.1016/0550-3213%2884%2990365-1)
is historical context for six-fermion/generation classifications. It is not
the source of the Li printed seeds used above. No convention, basis-span or
arbitrary-generation correspondence to Rao–Shrock is certified here; only
publisher metadata/abstract scope was checked for this citation. The
[Li coverage ledger](../../../../verification/li-basis-coverage.md) owns the
actual selected comparison and its extension boundary.
