# Compact Spin standard chain

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

External reference roles and the stage 02 bibliographic checks are recorded
in the [individual reference review](../../../REFERENCE_REVIEW.md).

## 1. Result and status

Updated: stage 01

### Checked Construction

For every n, `SpecialUnitaryRealification.hom` is an actual continuous
injective closed embedding SU(n) -> SO(2n). The source is the unitary
matrix group with determinant one. The target preserves the same positive
quadratic form used by the compact real Spin projection.

The real coordinates put all real parts first and imaginary parts second.
Conjugating the complex defining action by this real-linear coordinate
equivalence preserves the sum-of-squares form. Its real determinant is the
field norm of its complex determinant, hence one. No orthogonality,
orientation, continuity, or embedding certificate is a source premise.
The n = 5 specialization is `CompactSpin.realification`.

The generic `CoveringHom.existsUnique_lift` starts from a covering group
homomorphism and a continuous homomorphism from a simply-connected, locally
path-connected topological group. Mathlib supplies a continuous based lift.
Uniqueness of lifts on the connected product of the source with itself
proves multiplicativity. Injectivity follows whenever the original map is
injective. This general lemma has no ambient GUT imports.

Applying it to the actual compact Spin double cover gives the original
`exists_SU5_inclusion_of_topology`, retained for compatibility. The stronger
`exists_SU5_inclusion_of_simplyConnected` derives local path-connectedness
and has one explicit mathematical premise:

```text
SimplyConnectedSpace (Matrix.specialUnitaryGroup (Fin 5) Complex)
```

**SPIN-1d proves this premise** in `Math/LieGroups/SpecialUnitary/SimplyConnected.lean`.
`CompactSpin.SU5Inclusion` applies that result to the lifting theorem, so
the resulting inclusion has no assumed topology certificate. Its composition
with the Spin projection is exactly `realification`. It is a closed embedding
and the unique continuous homomorphic lift of that map. A nonidentity SU(5)
matrix, obtained by adjoining three unit coordinates to SU(2)'s `-I`, has
nonidentity image in Spin(10).

## 2. Inputs and conclusion

### Checked Selection-Rule Endpoint (SPIN-1)

`CompactSpin.StandardChain.Model` specializes the existing model to this
actual inclusion. Its inputs are unchanged:

- a finite-dimensional complex unitary representation of `Spin(10) x H`,
  with `H` an arbitrary Abelian group (including finite groups);
- a complex-bilinear symmetric mass invariant under the pulled-back
  SU(5) torus times `H`, not necessarily the full ultraviolet gauge group;
- finite nonnegative SM charge profiles of common positive total and the
  exact dual character target for the mass radical, with singlet data.

The theorem derives neutral supported `qque`/`duql` signatures and hence
refutes prohibition of every supported physical Delta B = 1 signature.
The continuous wrapper requires a jointly continuous ambient action, but
derives continuity and injectivity of the inclusion. The scalar-family
wrapper preserves the existing equivariant mass-family interface.

The inclusion is unconditional mathematical data; this physical endpoint
is conditional on the listed model inputs. The separate half-spin benchmark
constructs an inhabitant, without making the target automatic for all
matter. The common endpoint does not assert full-SM
invariant tensors on a general radical, a nonzero coefficient/amplitude,
an exact SM vacuum, or classification of other Spin(10) embeddings.

## 4. Proof structure

### Checked SU Topology (SPIN-1b)

For every positive rank, multiplying a unitary matrix by the diagonal
matrix `diag(conj(det g), 1, ..., 1)` gives a continuous retraction
U(n) -> SU(n). It is surjective and a quotient map by compactness and the
Hausdorff property. Mathlib's local path-connectedness of the unitary group
therefore descends to SU(n), in the actual matrix topology. The empty-rank
case is also checked. This retraction is **not a group homomorphism**;
an explicit U(2) counterexample is part of the audit.

The subgroup of SU(n+1) fixing the last standard vector is exactly the
image of the existing block inclusion `A -> diag(A,1)`. Unitarity forces
both the last column and row, and determinant one descends to the upper
block. The continuous block inclusion is a compact-to-Hausdorff bijection
onto that stabilizer, giving a **topological group equivalence** with SU(n).
The inverse is proved to extract the upper block. A concrete SU(2) matrix
outside the stabilizer guards against confusing it with the whole group.

The stabilizer theorem supplies the fiber identification used below.

### Checked Sphere Charts (SPIN-1c)

For every m >= 2, the last-column map from actual SU(m) to the Euclidean
unit sphere in C^m is continuous and surjective. This is the Euclidean
sphere `Metric.sphere (0 : EuclideanSpace ...) 1`, not the sphere for the
coordinate sup norm.

There are two explicit open patches covering the whole sphere. On the
north patch put `q = e_last + v`, `c = 1 + conj(v_last)`, where `c != 0`.
The rank-one formula `U = -I + c^(-1) q q*` is proved unitary and sends
`e_last` to `v`. Multiplication **on the right** by
`diag(conj(det U), 1, ..., 1)` makes its determinant one while preserving
the last column. The distinction from the earlier left retraction matters.
The second section applies the construction to `-v`, negates the unitary
matrix, and then corrects its determinant. Both sections are continuous
on their domains, and the domains are proved to cover the sphere.

For any of these sections `s` on `V`, the coordinate map is
`g -> (projection g, s(projection g)^(-1) * g)`. Its second component fixes
`e_last`. The inverse multiplies the section by the stabilizer element.
Continuity and both inverse identities are checked, and the preceding
stabilizer equivalence gives `projection^(-1)(V) ≃ V x SU(m-1)`.
`exists_localProduct` proves this over an open neighborhood of every base
point, preserving the actual projection as the first factor. These are
homeomorphisms, not group isomorphisms or a claimed global product.

This supplies a local product atlas, not a bundled mathlib `FiberBundle`
instance or a homotopy-lifting theorem. The separate argument below closes
simple-connectedness without needing either construction.
The rank bound is audited: SU(1) -> S^1 is **not** surjective.

### Checked Simple-Connectedness (SPIN-1d)

`specialUnitary_simplyConnected n` proves simple-connectedness of the actual
complex matrix SU(n) for every n, including the empty rank and SU(1).
The proof does not install an assumed topology or use a classification of
compact Lie groups.

The section domains are identified with spheres minus one pole; TauCeti's
punctured-sphere contraction makes them contractible. Their total-space
preimages are consequently homotopy equivalent to SU(n-1). Stereographic
projection identifies the two-pole complement with a punctured real
hyperplane, whose path-connectedness follows from its dimension. This
proves path-connectedness of the overlap upstairs whenever the fiber is
path connected.

The new group-independent `SimplyConnectedUnion` theorem glues two open
simply-connected sets with path-connected intersection. It subdivides each
path using mathlib's finite open-cover partition of the unit interval,
and transports homotopy classes through the pieces. The intersection
paths identify the two choices of based path classes. Induction from the
actual one-point SU(1) now closes all ranks. Persistent controls include
a real-line open cover and a discrete two-point counterexample with empty
overlap, as well as SU ranks 0, 1, 2, and 5.

## 6. Scope and limitations

### Current Boundary

**SPIN-1 and SPIN-2 are LEAN-CHECKED.** An actual continuous
injective SU(5) -> compact Spin(10) homomorphism is constructed, with closed
image and no outstanding source-topology premises. The shared standard-chain
selection-rule theorem is specialized along it. The exact light target is
still a physical-model input for arbitrary matter. The separate
[actual half-spin benchmark](SPIN_HALF_SPIN.md) now derives this target
and constructs a continuous model with zero mass and trivial residual action.
An SO(10) inclusion is a prerequisite, not a replacement for the Spin inclusion.
Spin(10) is distinct from the compact symplectic USp family in the preceding
[chirality milestone](COMPACT_SYMPLECTIC_CHIRALITY.md).

The compact carrier is TauCeti's `realCliffordSpinGroupZero 10`, the Spin
group of the positive-definite real quadratic form of signature (10,0),
with its Clifford-algebra subtype topology. It is neither split Spin(5,5)
nor a complex algebraic Spin group. Compactness, path-connectedness, and
the continuous surjective two-sheeted projection onto SO(10) are checked
by compiling and auditing the pinned upstream proofs. The projection is
proved noninjective, so it cannot be silently used in the reverse direction.

### Next Milestone

The approved SPIN-1/2 gates are complete. The next scheduled work is the
bounded compact-E6 feasibility audit in the
[ambient-group plan](../../../../topics/self-dual-chirality/plans/SELF_DUAL_AND_AMBIENT_GROUP_PLAN.md), not a new claim
about realistic Spin masses or vacuum dynamics.

The classical sphere-fibration induction is described in
[Jonny Evans's Lie-group topology lectures](https://jde27.uk/lgla/16_topology_accessible.html).
This guided the checked topology proof; the reference is not a Lean axiom.

The distinction from amplitudes, vacuum dynamics, nonstandard embeddings,
and a general classification of GUT groups is unchanged. Verification and
declarations are in [the implementation record](interfaces/spin-chain.md).

## 7. Sources and verification

### Pinned Library Audit

Reusable and compiled: TauCeti's compact-real Clifford Spin carrier,
compactness, path-connectedness, exact two-element fibers, and covering
map; mathlib's continuous based lifting and uniqueness; determinant under
restriction of scalars; finite-dimensional linear-map continuity.
SPIN-1b additionally reuses mathlib's C-star-algebra unitary-group local
path-connectedness and its descent along quotient maps.

A bounded search of the pinned mathlib, TauCeti, and project sources did
not locate SU(5) simple-connectedness or a ready-made
SU(n) -> compact Spin(2n) inclusion. This is a search result,
not a claim that no such implementation exists anywhere. Dependencies were
not upgraded or edited.

SPIN-1c reuses matrix rank-one identities, determinant/unitary APIs, and
homeomorphisms. TauCeti has `AlgebraicTopology/Sphere/SimplyConnected.lean`;
its sphere theorem was a candidate input to the induction, not
a proof about the total SU space. A bounded search did not find a ready
bundle simple-connectedness or open-cover gluing theorem for this step;
SPIN-1d implements the needed two-set gluing theorem in this project.
It reuses the punctured-sphere contraction, not the full sphere theorem.

TauCeti's polarized spin action and half-spin dimension theorem are now
connected to the actual compact-real carrier in the separately checked
[SPIN-2 construction](SPIN_HALF_SPIN.md). This gives the continuous unitary
16 and its character `1 + 10 + bar5` on the actual SU(5) inclusion, including
singlet cancellation in the dual index, and an actual positive-target
continuous model with zero mass and trivial residual action. Its full
torus/residual spectrum is one SM generation plus one neutral singlet.

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
