# Concrete S3 and Certified Irreducible LFV Blocks

## Concrete nonabelian action

S3 is the full permutation group of Fin 3, acting on complex triples by inverse
coordinate reindexing. Adjacent swaps do not commute. Kernel-checked generator
relations and six normal forms certify the finite group used in the example.
For every actual intertwiner f, permutation covariance proves

    f(x) = (d-o)x + o * (sum x) * ones,

where d and o are its diagonal and off-diagonal matrix entries. Both identity
and the constant-sum map are proved intertwiners. Therefore actual selected
B/W dipole allowance is equivalent to

    ell(mu) != 0 or (sum mu) * ell(ones) != 0.

The vanishing criterion is the conjunction of the two zero evaluations.
This includes zero selectors; an off-diagonal basis transition is explicitly
allowed. No standard-subspace irreducibility, numerical centralizer dimension
or UV model is a premise. See
[S3DipoleSelection](../../../Physics/StandardModel/Operators/S3DipoleSelection.lean).

## General finite irreducible decomposition input

Supply actual source/target equivalences to finite products of finite-dimensional
complex irreducible blocks. Blocks may repeat and their carriers may differ.
The implementation uses actual equivalence of block representations to decide
which pairs match, rather than assuming a common label means equivalence.

FiniteBlockHom proves the rectangular block-Hom equivalence, including empty
products. IrreducibleHomScalar identifies every matching Hom with a scalar
multiple of a chosen actual bridge using Schur; unmatched Hom spaces are zero.
IrreducibleBlockCoordinates constructs the full linear equivalence to complex
coordinates indexed by matching block pairs and proves its matrix units span.
Neither a Hom basis nor a spanning assumption is supplied by the caller.

SemisimpleDipoleSelection transports those units back to the original flavor
representations. Actual selected allowance iff one matrix-unit evaluation is
nonzero; prohibition iff all are zero. This keeps the internal irreducible
pairing and selector support, not merely a shared-constituent test. Repeated
blocks supply the usual multiplicity matrices. Classical bridge choices are
permitted; an executable decomposition/matching algorithm is not claimed.

The CyclicSemisimpleDipoleControl proves that actual scalar cyclic modules
are irreducible, constructs their decomposition equivalence, and connects the
new matrix-unit criterion to the previous arbitrary-selector charge/support iff.
Thus the generic adapter has a concrete checked consumer. The S3 example uses
its independently proved centralizer criterion; an explicit trivial/standard
S3 decomposition is not newly certified or needed for that result.

The [S3](s3-contract.md) and [block](block-contract.md) contracts are complete
at these scopes. A bare semisimplicity assertion is not an automatically
computed decomposition. Arbitrary nonsemisimple/weight-only classification,
generated-coefficient matching and physical LFV rates remain excluded.
