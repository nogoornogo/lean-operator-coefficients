# Heeck–Le six-quark structural replacement

The two literal Heeck–Le contractions, their selected exchange words and all
existing local-basis, statistics and physical-Hom statements are preserved.
Stored projected-source, forward-matrix and inverse-matrix arrays have been
replaced by source recipes and symbolic reconstruction. See
[verification](heeck-replacement-verification.md).

## Source and coordinates

[The recipe](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkRecipe.lean)
uses the color vectors `(-1,0,0,-1,1)`, `(-1,0,-1,0,1)` and Weyl pairing 0.
The existing polynomial epsilon identities still identify them with the two
printed contractions. The original 25 source/word choices are unchanged.

[Block normalization](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkBlocks.lean)
rescales the two spin coordinates by 12 and the three spin coordinates by 4.
The resulting sources are separated products of integer vectors. This is an
internal coordinate change, not a rescaling of the physical contractions.
The color-complement source has zero color-pair block for every exchange word;
[this support statement](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkSupport.lean)
is proved structurally, not by checking thirteen evaluated columns.

## Reconstruction

[The quotient solver](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkQuotient.lean)
recovers twelve source-1 coefficients from ten color-pair coordinates and two
explicit kernel parameters. [Its source connection](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkQuotientConnection.lean)
is a uniform identity in all twelve coefficients.

Five source-0 pairs split by sums and differences into even and odd directions.
[Pair solvers](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkPairSolvers.lean)
and [their actual-word connection](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkPairConnection.lean)
recover those five directions inside the six- and nine-dimensional blocks.
Three unpaired source-0 words and the two quotient-kernel combinations remain.
Their [five residual equations](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkCouplingConnection.lean)
are

\[
 y=\bigl(6(z_3-z_2),\;4(-z_0+z_2+z_4),\;
 2z_2+2z_3-4z_4,\;4(z_4-z_0),\;4(z_0+z_1)\bigr).
\]

They are solved successively by

\[
 z_2=(y_1-y_3)/4,\quad z_3=y_0/6+z_2,\quad
 z_4=(z_2+z_3)/2-y_2/4,\quad
 z_0=z_4-y_3/4,\quad z_1=y_4/4-z_0.
\]

[Extraction](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkExtraction.lean)
composes these stages as linear maps and proves reconstruction for arbitrary
25-component assembly coefficients. [The matrix presentation](../../../Physics/StandardModel/Operators/HeeckLeSixQuarkMatrix.lean)
then derives the left inverse; the generic square-matrix theorem gives the
right inverse. No evaluated matrix-product certificate enters this derivation.

## API and limits

`rationalSeedCoordinates`, `basisRational`, `inverseRational` and the rational
inverse theorem names remain as compatibility wrappers around the derived
maps. Their names do not denote stored tables. The obsolete stepping cache and
its closed checker are removed. Small index/scalar checks remain explicit.

The general algebraic reconstruction is over a field of characteristic zero;
the physical comparison still uses the existing complex representations and
typed flavor slots. There are 25 constrained local coordinates, not 25 free
Wilson coefficients. No new assumption, flavor restriction, UV matching,
generation mechanism, rate or paper-wide classification is introduced.
The remaining SU(6), example and E6 phases are recorded in the
[bounded plan](remaining-families-plan.md).
