# Compact symplectic chirality obstruction

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

Updated: stage 01

### Checked Scope

**SP-1 and SP-2 are LEAN-CHECKED.** The carrier is the closed subgroup of U(2n)
preserving the standard complex alternating form, conventionally USp(2n)
or Sp(n). It is compact and embeds continuously and injectively into
SU(2n). It is not the real split symplectic group or the full complex
algebraic symplectic group.

For every natural n, the actual continuous injective torus homomorphism is

```text
z |-> diag(z_1, ..., z_n, z_1^-1, ..., z_n^-1).
```

The matrix `J = [[0,-I],[I,0]]` belongs to this compact group and conjugates
each such torus element to its inverse. This is an equality of actual
group elements, not an assumed Weyl action on a character model. At positive
rank J has square -I; it must not be called an involution. SP-2 proves that
every group element is conjugate into this torus, including rank zero.

Consequently every finite-dimensional complex source representation has
equal character and dual character on the entire group. Finite integer
combinations of actual characters are inversion invariant too. Continuity
or unitarity of the source is not needed for this conjugation argument;
physically admissible continuous unitary sources are included.

For any invariant symmetric mass on the restricted representation, the
radical has zero dual character difference, by the existing mass-index
conservation theorem. This does not imply an empty radical, or a
nondegenerate symmetric mass for every pseudoreal source.

## 4. Proof structure

### Arbitrary Restrictions

For any group K and any homomorphism `i : K -> USp(2n)`, the restricted
source character equals its dual. The mass need only be invariant under K,
not under the ultraviolet group. Every finite-dimensional invariant
complex-bilinear symmetric mass therefore has zero gauge dual radical index.
Neither an SU(5) factorization nor a selected SM embedding is needed.

`no_positive_SM_target` combines this with DUAL-2: for an explicitly supplied
test torus and faithful SM weight evaluator, no such radical can have the
specified positive exact SM dual target after forgetting residual charges.
Arbitrary finite charge profiles, torsion charges, singlets, and additional
vectorlike matter retain the previously checked interpretation. Gauge-only
self-duality is not promoted to charge-resolved self-duality.

The existing `StandardChain.Model` is also impossible for **any** supplied
SU(5) -> USp(2n) homomorphism (`not_arbitrary_model`). The chosen-chain result
below is preserved as an explicit embedding example and compatibility endpoint.

### Chosen SM Chain

The actual map `A |-> diag(A, conjugate A)` gives a continuous injective
U(n) -> USp(2n), hence also SU(n) -> USp(2n). Composing with the existing
standard SU(5) block gives, for every k >= 0,

```text
SM -> SU(5) -> SU(5+k) -> USp(2(5+k)).
```

The SU(5) torus factorization through the symplectic torus is proved.
DUAL-2's faithful gauge evaluator therefore applies to the existing
`StandardChain.Model`: no such model can satisfy its positive exact SM
dual light target. The theorem allows arbitrary finite-dimensional source
matter and an invariant symmetric mass, not just defining-representation
samples. Residual Abelian groups, including finite ones, and finite SM
charge profiles are retained; charges are forgotten only in the contradiction.
Gauge singlets and vectorlike pairs do not remove that contradiction.

This excludes a specified light spectrum for the chosen chain. It is a
**chirality obstruction**, logically different from the SU(N) supported
operator selection-rule obstruction. No coupling, amplitude, vacuum, or
proton-lifetime conclusion is added.

### SP-2 Spectral Foundation

On the actual defining vector space, `quaternionicMap v = J conjugate(v)`
is conjugate-linear, squares to -1, preserves the Hermitian pairing up to
conjugation, and commutes with every compact symplectic matrix. A nonzero
v and its image are orthogonal and linearly independent.

Every element at positive rank now has an actual nonzero eigenvector pair
with eigenvalues z and z^-1 on Circle. This follows from complex eigenvalue
existence, proved unitarity of the defining action, and the quaternionic
identities. No diagonalization certificate is assumed. Independence also
holds at z = 1 or -1, not only for distinct eigenvalues. The pair's Hermitian
orthogonal complement is preserved by both the matrix and quaternionic map.

The checked generic theorem packages these properties as `QuaternionicSpectral.Data`
on an arbitrary complex inner product space, with coordinate-free subspace
restriction. A finite paired orthonormal frame of maximal size spans: its
orthogonal complement would otherwise produce another normalized eigenpair.
This yields a complete paired orthonormal eigenbasis and even complex dimension.

The data are constructed from each actual compact symplectic matrix, not
assumed for arbitrary source representations. The basis change matrix is
proved unitary and to satisfy `A J = J conjugate(A)`, hence symplectic.
Its eigenvector equations give actual conjugacy into the standard torus.
Conjugating the torus inversion element back gives an inverse conjugator
for each group element. The conjugator depends on the element: the fixed
J from SP-1 provably does not invert every group element.

Only after this matrix proof do arbitrary finite-dimensional source
representations enter, through trace conjugacy invariance and mass-index
conservation. There is no assumed all-representations self-duality,
torus conjugacy, or source Laurent-polynomial certificate.

## 6. Scope and limitations

### Remaining Boundary

This is an obstruction to the declared finite-dimensional light spectrum,
not a proton-decay theorem or a vacuum-selection result. It does not cover
strongly coupled/composite chirality mechanisms, classify all compact groups,
or separately identify other global forms of the symplectic group. Spin(10)
and E6 remain independent roadmap branches. The faithful target evaluator
and exact light-target condition remain explicit physical-model interfaces.

## 7. Sources and verification

### Library Reuse

The bounded pinned-source inspection checked TauCeti's SU(2) torus conjugacy,
its defining symplectic representation and quaternionic-structure API,
mathlib's Hermitian spectral API, and the project's unitary character
decomposition. No directly reusable arbitrary-rank compact symplectic
conjugacy theorem was located; this is a search result, not a theorem about
the absence of such a library. The completed direct paired-spectral route
needs no highest-weight classification or compact Lie-group machinery.

Pinned-library reuse: mathlib supplies `Matrix.symplecticGroup`, `Matrix.J`,
unitary matrices and block identities; TauCeti supplies compactness of the
unitary group. Its defining symplectic representation supplies an audit
control and the SP-2 defining-action foundation, not the SP-1 proof for
arbitrary representations. Mathlib's eigenvalue existence, orthonormal-basis,
subspace, and matrix APIs support the new spectral proof. No dependency pins
or trust axioms were changed.

Declarations and persistent controls are in the
[formalization record](../../inputs/Math/interfaces/compact-symplectic.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
