# Normalized Li D.9 Qqql Basis Certificate

## Result

The normalized local contraction in Li et al., appendix D.9, generates the
independently defined derivative-free degree-(3,1) qqql exterior coefficient
sector. The proof includes literal contraction agreement, exterior descent and
two-sided nonredundant flavor reconstruction, not just a matching count.

Sources: [conventions](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/LiQqqlConvention.lean),
[exterior certificate](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/LiQqqlExterior.lean),
[finite coordinates](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/QqqlFiniteFlavor.lean).

## Inputs And Citation Role

Q and L are complex modules with specified representations of an arbitrary
abstract residual group H. No compactness or continuity is required. Finite
coordinates additionally use supplied bases indexed by Fin n and Fin m;
actual field carriers require supplied equivariant identifications.

The [pinned v2 paper, PDF page 50](https://arxiv.org/pdf/2201.04639v2#page=50)
supplies the L,Q,Q,Q expression and its three flavor symmetry labels. It is
not a completeness premise. Brackets are interpreted as normalized alternating
spinor pairings; gauge epsilons are determinant pairings. This is a local
algebraic interpretation, not an LSZ or amplitude normalization theorem.
The [dictionary](../../../../topics/li-qqql-basis/source-recovery.md) records the
slot ordering and sign conventions explicitly.

## Proof Structure And Normalization

`fermionic_reorder` includes the odd move of L past three Q fields. The
spinor pairing uses the third pairing, cross minus direct. The resulting local
seed has coordinates `(0,0;1,-1)`, not `(0,0;-1,1)`.

The independent local-coordinate inverse decomposes into symmetric T,
alternating U and mixed V components. V is symmetric in its final two Q
inputs and has zero cyclic sum; its partner is V with the first two inputs
swapped. These equations are necessary and sufficient.

`source = -T - U/3 + V` fixes the normalization. `orbit_inverse` and
`source_orbit` prove the exact six-permutation reconstruction. `candidate`
is defined by raw exterior alternatization of this literal seed, independently
of the completeness inverse. `restriction_candidate` proves contraction
agreement on pure tensors, and `candidate_eq` identifies it with that inverse.
`every_sector_is_candidate` and `candidate_injective` prove exhaustiveness
and uniqueness. Raw alternatization is not silently divided by a factorial.

## Finite Basis And Dimension

Sorted weak triples index the symmetric component, strict triples the
alternating component. Mixed coordinates consist of distinct ordered pairs
and two entries per strict triple; all other entries are reconstructed by the
exchange and cyclic equations. Both extraction/reconstruction identities hold.

For arbitrary H the finite space retains exactly the intertwining equations
on reconstructed functionals. For trivial residual action all coordinates
are admissible: `flavorBasis` is independent and spanning. Each basis member
is a literal-seed candidate by `every_sector_is_candidate`.

The dimension is
`m * (choose(n+2,3) + choose(n,3) + n*n-n + 2*choose(n,3))`.
Three Q and three L flavors give 57; no conjugate doubling is included.
Flavor counts alone do not determine the invariant dimension for general H.

## Scope And Verification

This certifies the normalized D.9 local family with an explicit coordinate
choice, not ABC4EFT runtime arrays or a general Young-tableau algorithm.
The full p/y/m/j construction, amplitude correspondence, derivatives, EOM/IBP,
four-family total and physical rates are not claimed.

The [strict audit](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/Audit/AuditQqqlFlavorComponents.lean)
checks transitive axioms and import layers. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted. Exact finite sign/cardinality checks are Lean
kernel proofs, not external premises. Commands and full-build evidence are
recorded in the [topic](../../../../topics/li-qqql-basis/README.md).
