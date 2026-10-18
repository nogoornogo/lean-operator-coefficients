# SU2 Symmetric-Power Tensor Decomposition

## Exact result

For every pair of natural degrees h,d, the actual defining SU2 doublet H
and its algebraic dual satisfy an equivariant linear equivalence

    Sym^h H tensor Sym^d Hdual
      equiv direct sum over 0 <= r <= min(h,d) of Sym^(h+d-2r) H.

[SU2ClebschGordan.dualEquivalence](../../../Math/RepresentationTheory/SU2ClebschGordan.lean)
is the theorem's constructed equivalence. The finite sum is represented by
the dependent finite product of its constituent carriers with their actual
componentwise SU2 action. No degree cutoff, supplied decomposition, character
identification, source semisimplicity or nonzero-coefficient premise is used.
Degrees zero are included. `degree_eq` identifies the implemented natural
expression (h-r)+(d-r) with h+d-2r.

The tensor of two ordinary symmetric powers is proved first by `equivalence`
in the opposite orientation: constituent sum to the tensor. Explicit epsilon
duality then yields `dualEquivalence` in the displayed orientation. Both are
`Representation.Equiv`, not only vector-space equivalences or trace identities.

## Constructed maps

[SymmetricPowerOperations](../../../Math/RepresentationTheory/SymmetricPowerOperations.lean)
proves natural multiplication and symmetrized splitting of symmetric powers.
Multiplication concatenates pure slots and descends through both quotients.
Splitting averages all permutations with inverse factorial normalization;
on a pure power v^(p+q) it is exactly v^p tensor v^q. Actual group covariance
is proved for each operation, including the block multiplication that groups
two left and two right factors. Arbitrary complex source modules are supported.

[SU2SymmetricEmbeddings](../../../Math/RepresentationTheory/SU2SymmetricEmbeddings.lean)
starts from

    omega = e0 tensor e1 - e1 tensor e0.

Its SU2 invariance is proved from the determinant-one matrix identity. The
tensor is transported to the degree-one symmetric powers and multiplied
recursively to construct omega^r in Sym^r H tensor Sym^r H. For the r-th
constituent, split Sym^((h-r)+(d-r)) H and multiply by omega^r in the two blocks.
This constructs an actual equivariant map into Sym^h H tensor Sym^d H.

Each map is proved nonzero by a uniform evaluation. Use v=(1,1) for the
source pure power, the first coordinate functional in the left block and
the second in the right. The evaluated embedding is exactly 1 at every
degree. Irreducibility therefore makes every constituent map injective;
no matrix rank computation or assumed surviving raw tensor is used.

## Independence and completeness

[DistinctIrreducibleAssembly](../../../Math/RepresentationTheory/Decomposition/DistinctIrreducibleAssembly.lean)
is a reusable algebraic result: nonzero maps from finite-dimensional
irreducible representations with pairwise different dimensions assemble into
an injective map from their finite product. No target semisimplicity is needed.
A hypothetical nonzero kernel contains an irreducible subrepresentation.
Projection to one source constituent is an isomorphism; the other projections
vanish by Schur and different dimensions. This contradicts the chosen
constituent's injectivity.

SU2 symmetric-power irreducibility and dimension n+1 are directly reused
from the pinned TauCeti proofs. The constituent degrees are pairwise distinct.
`dimension_sum` proves their dimensions sum to (h+1)(d+1), the tensor's
dimension. Finite-dimensional injectivity and equal dimension give surjectivity.
`ofBijective` supplies the actual inverse and its two inverse identities.

[SU2DoubletDuality](../../../Math/RepresentationTheory/SU2DoubletDuality.lean)
constructs the epsilon map v -> (w -> v0*w1-v1*w0), proves its injectivity
and determinant-one covariance, and obtains the actual doublet/dual
representation equivalence. Its induced symmetric-power equivalence closes
the dual-Higgs tensor statement.

## What this closes and what remains

The missing actual SU2 carrier decomposition identified in the
[preceding checkpoint](remaining-reduction-results.md) is now proved.
The proof bypasses Lie/group integration and character-based reconstruction.
It provides the finite weak constituents required by a later coefficient
space reduction with nontrivial weak sources.

This result restricts the group to SU2. It does not set hypercharge or residual
actions to zero, or prove their compatibility with the chosen constituent
embeddings. It does not supply a decomposition of every fermion source, nor
the joining equivalence between typed scalar patterns and split symmetric
powers. The complete fixed-input SM support classification therefore remains
open. No UV realization, VEV, mass, quantum, derivative/EOM/IBP, matching or
rate assertion follows from this decomposition alone.

## Verification

All 73 new public declarations are registered in the existing strict Math
audit. Focused builds and that audit pass with default heartbeats and unchanged
dependency pins. The [verification record](verification.md) contains the
full build and repository checks. Work stays on the approved topic branch;
no master merge or push is authorized.

## Subsequent full-group and full-field connection

[Full Higgs connection](full-higgs-connection-results.md) now proves the
original fixed scalar-count/full-carrier equivalence to split symmetric powers
and retains the actual SM hypercharge factor in every weak constituent.
This closes those presentation/action obligations from the earlier checkpoint.
Classification of every fermion source's invariant Hom support, and a uniform
all-degree reduction for all contents, remain separate obligations.
