# Reconstructing complete spin sums from actual weight spaces

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, integration
target `master`; no merge or push authorized. This implements the reconstruction
interface in the [completion plan](colored-support-completion-plan.md).

`SU2WeightsDetermine.equivalence` proves that actual retained-action
equivalences of nonnegative circle-weight spaces through N+2 reconstruct a
full SU2 x K equivalence to the proposed bounded isotypic sum. The source
requires proved joint continuity and torus bound N. Its complete isotypic
decomposition is constructed by the existing theorem. Consecutive actual
slice equivalences and finite-length cancellation identify each multiplicity.
K need not be compact or semisimple.

`SU2GroupStrings.equivalence` groups any finite family of strings by its
degree, preserving dependent retained carriers and repeated labels.
`reconstruct` therefore accepts a positive list of proposed strings directly;
missing degrees require no artificial zero-padding. No character or numerical
dimension comparison replaces the actual weight-space equivalences.

`SU2ExteriorSliceModels` constructs a finite Hilbert copy of an actual
exterior-doublet source from its symbolic exterior basis. Its continuity
follows from existing basis-action and exterior-continuity theorems. Its
torus bound is proved from the two opposite doublet weights and Pauli capacity:

```text
min(n, 2 dim(A) - n).
```

The finite basis is used abstractly, without expanding its vectors or indexing
set. The copied source's actual weight spaces are identified with the same
exterior-power tensor products as in the
[algebraic source comparison](exterior-weight-slice-results.md).

The scalar-product and exterior-source modules also now prove absent-weight
vanishing, uniformly. Weights outside the doublet interval/parity string
vanish in the entire source and its Hilbert copy. These are vector identities,
not numerical multiplicity evaluations.

The new three modules and five extended lemmas add 27 strict transitive
checks. No Weyl formula, numerical certificate, branching, matching or
irreducibility premise is added. In a Q application, the actual finite slice
comparisons remain proof obligations; the reconstruction theorem does not
assume the desired classification. Their color/weak specialization and the
general positive restricted-color coupling rule remain the continuation.

See [verification](weight-reconstruction-verification.md).
