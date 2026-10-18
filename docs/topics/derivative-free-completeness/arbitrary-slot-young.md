# Arbitrary-Slot Statistics And Young Projectors

## Verified endpoint

The pinned TauCeti already constructs the arbitrary-index tensor permutation
representation and its commutation with diagonal tensor maps. The new adapter
uses this action on arbitrary complex flavor F with arbitrary residual H,
proves commutation with the residual tensor-power representation, and supplies
the symmetric and sign-twisted relation quotient equivalences in every degree.
The inverse-permutation convention is preserved on pure tensors.

For a specified Young tableau t of shape mu, TauCeti proves rational normalized
Young symmetrizer idempotence. Transporting this proved element to C and acting
on tensor power gives an equivariant idempotent. Its image is a residual
subrepresentation, its kernel is stable, and its kernel quotient is
equivariantly equivalent to its image. The kernel equals range(id-P), and image
and kernel are complementary. The normalization is the rational Specht ideal
dimension divided by |mu|!, not a scalar assumed from literature.

Sources:
[TensorPermutationStatistics](../../../Math/RepresentationTheory/TensorPermutationStatistics.lean),
[YoungTensorProjector](../../../Math/RepresentationTheory/YoungTensorProjector.lean),
[audit](../../../Math/RepresentationTheory/Audit/AuditYoungTensorProjector.lean).

## Upstream reuse and boundaries

Mathematical dependencies, not unchecked external premises:

- `TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic`: permutation action
  and commutation of its group-algebra extension with diagonal maps.
- `TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent`: normalized
  rational Young symmetrizer idempotence, transported by algebra homomorphisms.

These adapters require neither finite-dimensional flavor nor compactness.
They construct one tableau component, not a complete nonredundant decomposition.
Different tableau projectors must not be presumed orthogonal, disjoint or
jointly exhaustive. Proving the correct isotypic/multiplicity decomposition and
its local-contraction/statistics compatibility is still needed for p-basis.

Inspection also found pinned upstream Schur-Weyl image-centralizer theorems
for tensor powers of `Fin n → k`. These are not yet adapters in this topic;
their finite-standard-carrier hypotheses are not silently assigned to arbitrary
flavor modules. No p/y/m/j-basis enumeration, derivative or EOM/IBP theorem is
claimed by this milestone.

## Verification

The persistent audit checks 14 declarations transitively against standard Lean
axioms only. Full-build counts and integration status are in the topic overview.
