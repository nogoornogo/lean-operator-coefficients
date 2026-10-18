# Multiplicity spaces and centralizers

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Status

Generalization C is **complete**. The algebraic commutant and
general-linear centralizer are checked for arbitrary finite-dimensional
semisimple representations over an algebraically closed field. The unitary
block-coordinate model, its weighted determinant constraint, and continuity
are also checked. Every actual finite-dimensional unitary representation now
has a constructed isometric Hilbert multiplicity decomposition, and its U/SU
centralizers are topologically isomorphic to the explicit product of unitary
matrix groups and its full weighted determinant kernel:

```text
C_U(V)(rho(G))  ~= product_c U(m_c)
C_SU(V)(rho(G)) ~= { A in product_c U(m_c) | product_c det(A_c)^(dim S_c) = 1 }.
```

These are `ContinuousMulEquiv` constructions, with continuity in both
directions. The zero representation and repeated constituents are included.
Neither compactness nor a topology on the acting group is required; the
representation must preserve the supplied positive-definite inner product.

The labels A-C here refer to the generalization roadmap, not the historical
SU(6) proof labels. This work neither enlarges the physical no-go theorem nor
replaces the completed SU(6) two-torus centralizer classification.

### Algebraic Result

For a finite-dimensional semisimple representation `rho` of any monoid over
an algebraically closed field `k`, Lean constructs

```text
End_G(V) ~= product_c Matrix(m_c, m_c, k)
C_GL(V)(rho(G)) ~= product_c GL(m_c, k).
```

For group representations, the second source is proved equal to mathlib's
ordinary subgroup centralizer of the actual image in `GL(V)`. The monoid
version uses invertible endomorphisms commuting with all action operators.
No finite-group, compactness, continuity, or group-algebra semisimplicity
hypothesis is used. Only the represented module must be semisimple.

`Math/RepresentationTheory/Multiplicity/MultiplicityCommutant.lean` provides:

- `Model`: indexed by the actual nonzero isotypic components, with a simple
  constituent `S_c`, positive multiplicity `m_c`, and a proved module
  equivalence `c ~= (Fin m_c -> S_c)`.
- `exists_model` and `exists_representation_model`: construct this data
  from semisimplicity and finite dimension, rather than assuming a matrix
  classification certificate.
- `Model.component_finrank` and `Model.multiplicity_eq`: the copy count has
  the expected dimension formula and is independent of the chosen model.
- `Model.endAlgEquiv` and `commutantEquiv`: actual algebra equivalences,
  assembled from mathlib's `IsSemisimpleModule.endAlgEquiv`,
  `IsIsotypic.linearEquiv_fun`, `endVecAlgEquivMatrixEnd`, and Schur's lemma.
- `finite_components`, `commutant_finrank`, and `automorphismEquiv`: the
  component set is finite, the commutant dimension is `sum m_c^2`, and units
  correspond to products of invertible multiplicity matrices.

`CommutantCentralizer.lean` identifies the intertwiner algebra with the
centralizer subalgebra of actual linear operators. It then gives
`linearCentralizerEquiv` and `linearCentralizer_eq_groupCentralizer`.
These are abstract-group equivalences, not yet topological group equivalences.

## 4. Proof structure

### Unitary Source

`UnitaryMultiplicity.lean` contains the existing orthogonal-complement
semisimplicity proof, now independent of SU(6). The old declarations in
`CompactEmbeddingClassification.lean` remain as compatible aliases/wrappers.
No existing theorem or physical assumption is discarded.

`multiplicityModel` constructs the algebraic model for every finite-dimensional
complex unitary group representation. `linearCentralizerEquiv` then applies
the preceding GL result. Compactness is unnecessary once an invariant
positive-definite inner product is supplied.

The original algebraic decomposition is not assumed isometric. An arbitrary
algebra equivalence need not preserve adjoints and cannot simply be restricted
to unitary elements. The following new construction supplies that missing
inner-product step.

### Isometric Decomposition

`UnitaryIntertwiner.lean` proves `exists_isometric_intertwiner`: an algebraic
equivalence between finite-dimensional complex unitary representations of
any group can be replaced by an equivariant linear isometry equivalence.
The proof constructs the Gram operator `A = f.adjoint * f` and its positive
square root `S`. The adjoint is an intertwiner in the reverse direction;
therefore `A`, and then `S`, commute with the source action. Injectivity and
finite dimension make `S` invertible, and `f * S.inverse` is isometric.
The square-root and commutation theorems come from pinned mathlib's continuous
functional calculus. No compactness, continuity of the group action, or
nonzero-space hypothesis is added.

`IsometricMultiplicity.lean` applies this to the existing constructed model:

```text
V ~= PiLp 2 (c -> PiLp 2 (Fin m_c -> S_c)).
```

Here each `S_c` is the actual simple submodule chosen in `Model`, with its
inherited inner product. The target action is the group-algebra action on
each copy, and is proved unitary. `isometricEquiv` and
`isometricEquiv_intertwines` supply the isometry and its equivariance.
`constituent_finrank_pos` and `finrank_eq_sum` identify positive constituent
dimensions `n_c` and prove `dim V = sum m_c * n_c`.
The construction does not require distinct dimensions for distinct
constituents, nor does it assume a pre-existing isometric certificate.

### Topological Transport

`UnitaryCentralizerTransport.lean` defines `unitaryCentralizer rho` using
the actual unitary continuous linear operators commuting with every `rho g`.
For an equivariant isometry `e`, conjugation gives
`unitaryCentralizerEquiv`, a `ContinuousMulEquiv` with proved continuity in
both directions. `det_unitaryConj` proves equality of the actual operator
determinants. Restricting to determinant one yields
`specialCentralizerEquiv`, again two-sided continuous.

`IsometricMultiplicity.unitaryCentralizerEquiv` and
`IsometricMultiplicity.specialCentralizerEquiv` apply these results to the
constructed Hilbert multiplicity model. Their targets are intermediate
Hilbert-model centralizers. `MultiplicityUnitaryCentralizer` and
`MultiplicitySpecialCentralizer` now identify these with the matrix products
and kernel below and compose the equivalences back to the original space.
The entire determinant-one subgroup is transported; there is no restriction
to its identity component.

### Block Coordinates

`MultiplicityMatrix.lean` defines the concrete matrix action

```text
amplify(A) = blockDiagonal_c (A_c tensor I_(n_c)).
det(amplify(A)) = product_c det(A_c)^(n_c).
```

The block sizes may differ. `det_blockDiagonal'` supplies the dependent-block
determinant formula using mathlib's block-triangular determinant theorem;
`det_amplify` then uses the Kronecker determinant theorem. Its order on the
finite block index is only an indexing device.

The file proves multiplicativity and adjoint compatibility. If every
`n_c > 0`, amplification is injective and is unitary exactly when each `A_c`
is unitary. `unitaryMap` packages the product action as a continuous group
homomorphism. `weightedDet` is a continuous character and
`specialMultiplicityGroup` is its closed kernel. Membership is equivalent
to determinant one of the actual amplified matrix.

The integers `n_c` are explicit coordinate dimensions in this file. The
following bridge identifies them with the actual constituent dimensions;
the coordinate determinant formula is not used alone as a classification.

### Actual Centralizer Classification

`HilbertMultiplicityOperator.lean` implements scalar mixing on the Hilbert
sum: `(operator A x)_c,a = sum_b A_c,a,b x_c,b`. It proves that this is an
algebra homomorphism, that its true Hilbert adjoint is `operator (star A)`,
and that it is injective when each constituent is nonzero. Consequently the
operator is unitary if and only if each multiplicity matrix is unitary.
The matrix-to-operator map is a continuous closed embedding.

`MultiplicityUnitaryCentralizer.lean` proves that this explicit action
exhausts the full intertwiner algebra. Its injectivity and the dimension
equality supplied by the previously proved Schur classification yield
surjectivity. The original arbitrary algebra equivalence is used only for
dimensions, never assumed to preserve adjoints. `modelUnitaryEquiv` restricts
the explicit action to unitary elements, and proves inverse continuity using
the closed linear embedding. `unitaryCentralizerEquiv` then classifies the
centralizer of the original representation.

`HilbertMultiplicityDeterminant.lean` constructs actual constituent basis
coordinates and conjugates the Hilbert operator into the checked amplified
matrix. `det_operator` proves

```text
det(operator A) = product_c det(A_c)^(Module.finrank Complex S_c).
```

Ordinary bases suffice here: determinant is invariant under linear change
of basis. Adjoint compatibility was proved separately using the actual
inner products, so no arbitrary basis is asserted to be orthonormal.

`MultiplicitySpecialCentralizer.lean` uses this actual determinant identity
to restrict the topological equivalence to `specialMultiplicityGroup`.
Its `specialCentralizerEquiv` includes every element of the weighted kernel,
not just a connected subgroup or an unweighted determinant-one subgroup.

The public entry point `UnitaryMultiplicityClassification.lean` constructs
the model and finite component indexing from `rho` and its unitarity proof.
It requires no user-supplied decomposition, exhaustion, or classification
certificate. In namespace `Math.UnitaryMultiplicity`:

- `unitaryFactors` is the product of the actual multiplicity unitary groups.
- `determinantCharacter` uses actual simple-constituent dimensions.
- `specialFactors` is its full kernel.
- `unitaryCentralizerEquiv` and `specialCentralizerEquiv` are the two final
  topological group equivalences.

## 6. Scope and limitations

### Scope Boundary

The U/SU bridge is closed for finite-dimensional complex unitary group
representations. This does not assert a unitary classification for arbitrary
nonunitary actions, nor extend the existing algebraic GL theorem to a new
topological statement. The kernel is identified as a whole; computing its
connected components or choosing canonical coordinates is a separate result.

The existing [SU(6) centralizer dossier](HYPERCHARGE_CENTRALIZER.md) proves
the concrete multiplicity-free `3+2+1` case and remains valid independently
of this reusable generalization.

## 7. Sources and verification

### Audits

`AuditMultiplicityCommutant.lean` checks:

- Two repeated trivial constituents have a four-dimensional commutant and
  explicit noncommuting endomorphisms. Scalar phases alone are insufficient.
- The zero representation has a constructed model and zero-dimensional
  commutant; there is no hidden nonzero-space hypothesis.
- An actual GL-centralizer equivalence is instantiated on the repeated
  example, and the unitary-source model is checked with arbitrary group.
- For one copy of a two-dimensional constituent, the weighted SU kernel
  consists exactly of `+1` and `-1`. The unweighted determinant would wrongly
  discard the latter. No connectedness assumption is introduced.

`AuditIsometricMultiplicity.lean` additionally checks a non-isometric scalar
equivalence and the existence of its isometric replacement; constructs the
model and isometry for trivial representations of every dimension, including
zero and repeated constituents; and constructs an isometric equivariant
decomposition for a proved nontrivial two-coordinate permutation action.
It instantiates the U/SU topological transports and checks their continuity
and topological group instances. These are persistent audits, not temporary
files or assumed model certificates.

`AuditMultiplicityCentralizer.lean` checks the final API on zero and repeated
trivial representations and on the nontrivial permutation representation.
It checks both directions of continuity for arbitrary unitary sources. A
minus-identity multiplicity on a two-dimensional Hilbert constituent is
proved to be a nonidentity unitary operator of actual determinant one,
while its unweighted multiplicity determinant is minus one. The earlier
exactly-two-element kernel audit is retained.

Audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Dependency revisions are unchanged. Reproduce the checks with:

```bash
lake build Math.RepresentationTheory.Multiplicity.Audit.AuditMultiplicityCommutant
lake build Math.RepresentationTheory.Multiplicity.Audit.AuditIsometricMultiplicity
lake build Math.RepresentationTheory.Multiplicity.Audit.AuditMultiplicityCentralizer
lake build
```

Verification at stage 01: the algebraic milestone passed its targeted audit
(2961 jobs) and full build (4242 jobs). The isometric milestone passed its
new targeted audit (3088 jobs) and the full build (4249 jobs). The earlier
extraction required one explicit orthogonal-subspace type annotation in
`EquivariantMassIndex`; its theorem statements and the final physical
endpoint are unchanged. The new files contain no `sorry` or additional
axioms. Existing warnings elsewhere in the repository are not changed.
The final matrix-classification milestone passed its targeted audit
(3606 jobs) and full build (4255 jobs), with only the three standard axioms
in the audited declarations. The completion summary is in
[historical milestone record](../../../../topics/character-centralizer-foundations/checkpoints/generalizations.md).

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
