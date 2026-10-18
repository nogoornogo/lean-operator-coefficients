# From literal sources to small blocks

The replacement follows the actual multilinear coefficients, rather than
starting from an evaluated coordinate matrix.

1. [RawSource](../../../Physics/StandardModel/Operators/LiSixQuarkRawSource.lean)
   identifies four color diagrams and one Weyl diagram after the fixed slot
   relabelling. Their five-component reconstructions are polynomial epsilon
   identities on arbitrary input vectors.
2. [YoungOperators](../../../Physics/StandardModel/Operators/LiSixQuarkYoungOperators.lean)
   expresses the row/column actions as products of short generator sums. For
   example the alternating action on three down slots is
   \((1-t_1)(1-t_2+t_2t_1)\). These are the local, fermion-transferred actions;
   the row/column convention is not changed.
3. [YoungExpansion](../../../Physics/StandardModel/Operators/LiSixQuarkYoungExpansion.lean)
   equates those products with the literal 48-term source dictionary for an
   arbitrary function of six slots. [SourceTransport](../../../Physics/StandardModel/Operators/LiSixQuarkSourceTransport.lean)
   then identifies the actual multilinear coefficients. No projected seed
   values or basis inverse enter this bridge.
4. [SeedRecipe](../../../Physics/StandardModel/Operators/LiSixQuarkSeedRecipe.lean)
   transports the same recipe between exact scalar fields. Rational evaluation
   is a presentation of the complex coefficients, not a separate premise.
5. [ReducedAction](../../../Physics/StandardModel/Operators/LiSixQuarkReducedAction.lean)
   transports each generator through the explicit \(2+3\) coordinate changes.
   The resulting \(4+6+6+9\) product blocks are invariant. The
   [Young image profiles](../../../Physics/StandardModel/Operators/LiSixQuarkYoungImages.lean)
   give fixed directions multiplied by scalar functionals on arbitrary arrays.
   Each nonzero block needs just one such amplitude for a specified tableau.
6. [ReducedSeeds](../../../Physics/StandardModel/Operators/LiSixQuarkReducedSeeds.lean)
   specializes those uniform identities to the source diagrams.
   [SeedDirections](../../../Physics/StandardModel/Operators/LiSixQuarkSeedDirections.lean)
   derives their nineteen scalar amplitudes from the five-component sources;
   no projected array is supplied as a certificate. The trace of
   the first block explains the printed/extra separation. Short within-species
   exchange words then supply the selected orbit columns.
7. [BlockSolvers](../../../Physics/StandardModel/Operators/LiSixQuarkBlockSolvers.lean)
   and [BlockExtraction](../../../Physics/StandardModel/Operators/LiSixQuarkBlockExtraction.lean)
   solve the small blocks symbolically. Trace/alternating/standard components
   resolve the first block; sums and differences separate the mixed blocks;
   the final block has its own named scalar, triple, pair and triple coordinates.

The source permutation/weight dictionary is retained because it specifies the
literal convention being checked. It is distinguished from a cached evaluated
seed table or a proposed dense inverse. Small index, epsilon and scalar
identities remain exact algebraic checks. A tactic-name ban would not express
this distinction.

The ten printed contractions and the eleventh extension retain their separate
roles. Local reconstruction and printed-flavor coverage do not imply EFT
completeness beyond the stated derivative-free field content, UV generation,
matching coefficients or physical rates. Verification of the connected consumer
pipeline is recorded separately; the derivation map alone is not that check.

For example, source 0 has raw color vector `(0,0,1,0,0)` and raw spin vector
`(1,1,0,1,1)`. Their split coordinates are

\[
 C_2=(0,\tfrac12),\quad C_3=(-\tfrac12,0,\tfrac12),\qquad
 S_2=(-\tfrac16,\tfrac16),\quad S_3=(1,\tfrac12,1).
\]

Writing their product array as \(c\), the two amplitudes for its Young image are

\[
 a=c_{02}-3c_{03}+2c_{12}-3c_{13}=\tfrac14,
\qquad
 b=c_{20}+c_{21}-3c_{30}+3c_{31}-3c_{40}+3c_{41}=\tfrac12.
\]

The fixed image directions in `direction0` then determine the entire array.
This is the role of the small scalar checks: they connect an explained source
to uniform image formulas, rather than certify the rank of an unexplained
matrix of evaluated coefficients.
