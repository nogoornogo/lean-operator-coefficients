# Semisimple embedding classification

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

### Status

`LEAN-CHECKED DECOMPOSITION AND CENTRALIZER STANDARDIZATION FOR CONTINUOUS EMBEDDINGS WITH A NONTRIVIAL COMMUTING CONTINUOUS CIRCLE`

## 2. Inputs and conclusion

Let

\[
\iota:SU(3)\times SU(2)\longrightarrow SU(6)
\]

be an injective continuous matrix homomorphism.  Assume also that a nontrivial
continuous hypercharge circle in `SU(6)`
commutes with the image of `\iota`.  Then the restriction of the defining
six-dimensional representation has exactly three irreducible constituents: a
three-dimensional color constituent trivial under `SU(2)`, a two-dimensional
weak constituent trivial under `SU(3)`, and a one-dimensional singlet.
Symbolically, its semisimple decomposition is

\[
6=(3,1)+(1,2)+(1,1).
\]

Moreover, one `SU(6)` conjugator simultaneously carries the compact
centralizer of these actual constituents to the standard `3+2+1` block
centralizer used downstream.  This is the semisimple embedding classification conclusion consumed by the
centralizer construction and by the final assemblies involving character rigidity,
the charge-orbit bridge, and the scoped physical-model theorem.
It is a decomposition and centralizer standardization theorem, not a
classification of the full homomorphism up to ambient conjugacy.

## 4. Proof structure

**Lean update:** `GUT/SU6/Embeddings/SemisimpleEmbedding.lean` proves the finite dimension
count: after the standard low-dimensional irrep list is supplied, exactly the
three shapes `(3,2)`, `(3,1)+(1,2)+(1,1)`, and `(3,1)+(1,3)` remain.  It also
proves the general kernel obstruction for a subrepresentation that detects a
kernel element.  `GUT/SU6/Embeddings/CompactEmbeddingClassification.lean` proves that the
restriction of the defining representation along any
`SU(3) x SU(2) -> SU(6)` homomorphism is a finite-dimensional unitary, hence
semisimple, representation.  It constructs the correct weak-center element
`(1,-I_2)` and specializes the kernel obstruction.  Schur's lemma is used to
prove that an irreducible complex representation has no non-scalar commutant,
and Lean verifies that a scalar matrix in `SU(6)` has sixth-root coefficient.
`GUT/SU6/Embeddings/LowDimensionalIrreps.lean` proves the arithmetic consequence of the
`SU(3)` Weyl dimension formula through dimension six, the analogous `SU(2)`
dimension arithmetic, all possible product-block dimensions, and a sound
finite block-list-to-branch-count bridge.

`Math/RepresentationTheory/Decomposition/Burnside.lean`, `Math/RepresentationTheory/Decomposition/ProductIrreducibility.lean`, and
`Math/RepresentationTheory/Decomposition/ProductFactorization.lean` now prove both directions of the required
product-group theorem over `Complex`: external tensor products of irreducibles
are irreducible, and an irreducible product representation with semisimple
factor restrictions is equivalent to the external tensor product of
irreducible factors.  The converse uses the canonical multiplicity space,
Burnside density, and evaluation.  `Math/RepresentationTheory/Decomposition/CompactProductFactorization.lean`
supplies semisimplicity from unitarity and constructs continuous ambient
models for both extracted factors.
The SU2/SU3 differentiated highest-weight application of those factors is
retained in `GUT/SU6/Adapters/CompactProductClassification.lean`, under the
same `GUT.CompactProductFactorization` declaration namespace.

`GUT/SU6/Hypercharge/ContinuousCentralizer.lean` proves that a continuous circle in the
centralizer of an irreducible defining restriction is trivial: Schur makes it
scalar, the `SU(6)` determinant confines the coefficient to the finite sixth
roots of unity, and connectedness makes that coefficient constant.
`GUT/SU6/Embeddings/LowDimensionalConcreteIrreps.lean` directly proves irreducibility and
continuity of the defining color triplet; the corresponding facts for the
weak doublet and its center action are also Lean-checked.

`Math/RepresentationTheory/Decomposition/FiniteSemisimpleDecomposition.lean` now extracts an actual finite
direct sum of simple group-algebra submodules and proves that identities on
all constituents assemble to an identity on the ambient representation.  It
also packages the group-algebra decomposition as a `Representation.Equiv`
from the original representation to the direct sum of the actual blocks.
`GUT/SU6/Embeddings/WeakDoubletEmbeddingClassification.lean` classifies every constituent, constructs
the certified block list, eliminates `(3,1)+(1,3)` by the weak center, and
eliminates `(3,2)` in the presence of a nontrivial commuting continuous
hypercharge circle.  The conclusion now retains the classified irreducible
subrepresentations: their labels are a permutation of exactly
`[color3, weak2, singlet]`, there are exactly three constituents, and each
label has a unique constituent index.  Thus, conditional on either the legacy
full `SU2SU3HighestWeightTheory` interface or the sharper bounded
`SU2SU3LowDimensionalTheory`, Lean proves the actual restricted defining
representation has a semisimple decomposition of shape
`(3,1)+(1,2)+(1,1)`.  This is not yet a conjugacy classification of the
homomorphism itself.

`GUT/SU6/Hypercharge/ActualBlockConjugacy.lean` proves the geometric consequence of this
decomposition needed downstream in standard charge-orbit bridge: the three actual coordinate ranges
admit one ordered orthonormal basis, and after a determinant correction the
resulting `SU(6)` matrix simultaneously conjugates the entire actual compact
centralizer to the standard `3+2+1` diagonal block torus.  This closes the
fixed-conjugator dependency for centralizer characters while deliberately
leaving the stronger classification of the full semisimple homomorphism and
its possible source automorphisms unstated.

`GUT/SU6/SelectionRules/Audit/AuditEmbeddingClassification.lean` keeps the axiom audit for the main semisimple embedding classification dependency chain
under source control.  It can be rerun after cloning with
`lake env lean GUT/SU6/SelectionRules/Audit/AuditEmbeddingClassification.lean`; the audited theorems currently depend
only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or
additional project axiom.

`Math/Algebra/Lie/Sl2String.lean` proves the algebraic `SU(2)` dimension theorem rather
than assuming it: for a finite-dimensional irreducible complex Lie module
whose acting algebra is spanned by an `sl2` triple, the lowering string is a
basis and `dim = highestWeight + 1`.  `Math/Algebra/Lie/StandardSl2.lean` realizes that
triple as explicit trace-zero two-by-two complex matrices, proves its
relations and spanning theorem, and proves that every one-dimensional module
over this concrete Lie algebra has zero action.

The corresponding bounded `SU(3)` algebraic classification is now also
Lean-checked.  `Math/Algebra/Lie/StandardSl3.lean` defines the two simple-root triples
inside concrete trace-zero three-by-three complex matrices, verifies all root
relations, proves that the six simple generators span `sl3(Complex)`, and
proves that every one-dimensional module has zero action.
`Math/Algebra/Lie/StandardSl3Borel.lean` constructs the upper Borel and proves its third
derived term is zero.  Lie's theorem in
`Math/Algebra/Lie/Sl3HighestWeightExistence.lean` then supplies a common Borel
eigenvector; the root commutators and the two checked `sl2` integrality
theorems make its Cartan weights natural.  Finally,
`Math/Algebra/Lie/Sl3HighestWeight.lean` constructs enough lowering-string weight
vectors to prove unconditionally that every nonzero irreducible concrete
`sl3(Complex)` module of dimension at most six has dimension `1`, `3`, or `6`.
Thus semisimple embedding classification no longer depends on a separately assumed `SU(3)` Weyl dimension
formula.

`HighestWeightBridge.SU3StandardLieModel` connects that theorem to a group
representation, while `SU2SU3StandardLieTheory.toLowDimensionalTheory`
combines the checked `sl2` and `sl3` results into exactly the four bounded
facts consumed downstream.  The new theorem
`injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_standardLieTheory`
reaches the full semisimple embedding classification weak-doublet branch conclusion through this route.

`HighestWeightBridge.lieModule_isIrreducible_of_group_stable` now proves the
order-theoretic part of differentiation: an irreducible group representation
has an irreducible supplied Lie action whenever every Lie submodule is stable
under the original group action.  The structures
`SU2IntegratedStandardLieModel` and `SU3IntegratedStandardLieModel` omit Lie
irreducibility as input and derive it by this theorem.  Their combined theory
feeds the full semisimple embedding classification conclusion through
`injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_integratedLieTheory`.

`GUT/SU6/Embeddings/ExponentialRepresentationBridge.lean` now proves the general
finite-dimensional integration steps.  An endomorphism-invariant subspace is
preserved by its operator exponential, generator stability extends over finite
products, and generator actions equal to the identity extend to the whole
generated group.  It also proves that an operator exponential acts on an
eigenvector by exponentiating its eigenvalue, both for continuous
endomorphisms and for the chosen-basis finite-dimensional exponential.
Consequently, compatibility
`rho(exp X) = exp(d rho X)` on any finite-product exponential generating
family derives both Lie-submodule stability and the fact that zero
differential gives a trivial group action.  The structures
`SU2ExponentiallyIntegratedStandardLieModel` and
`SU3ExponentiallyIntegratedStandardLieModel` expose only this local data, and
`injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_exponentialLieTheory`
feeds it through the complete checked semisimple embedding classification branch argument.

`GUT/SU6/Embeddings/SpecialUnitaryExponential.lean` verifies by the concrete matrix
exponential that `exp(pi*i*H) = -I_2`, the nontrivial center element of
`SU(2)`.  `HighestWeightBridge.su2_center_eigenvalue_of_exponential` combines
this generator with the checked eigenvector-exponential formula to derive the
center sign `(-1)^n` on a highest-weight vector.  Therefore the sharper
`SU2GeneratedExponentialStandardLieModel` and
`SU2SU3GeneratedExponentialLieTheory` no longer accept the weak-center sign as
an independent field; they derive it from one distinguished exponential
generator.  The complete semisimple embedding classification branch theorem is checked from this sharper
interface and is included in `AuditEmbeddingClassification.lean`.

`Math/LieGroups/Matrix/MatrixDeterminantExponential.lean` proves the missing finite complex
matrix identity `det(exp A) = exp(trace A)`.  Using it,
`GUT/SU6/Embeddings/SpecialUnitaryLieAlgebra.lean` defines the concrete compact real form
as traceless skew-adjoint matrices and proves that its matrix exponential
lands in `SU(n)`.  It packages `pi*i*H` in this real form and checks that its
compact exponential is the same nontrivial `SU(2)` center element.  A
surjective exponential is converted to the finite-product generation object
already consumed by the integration bridge.

`GUT/SU6/Embeddings/SpecialUnitaryGeneration.lean` now proves the required generation
fact directly, without assuming that the compact exponential is surjective.
For every finite unitary matrix, finiteness of its spectrum makes the principal
argument continuous on that spectrum, so continuous functional calculus gives
a self-adjoint logarithm even when `-1` is an eigenvalue.  For an element of
`SU(N)`, `N > 0`, Lean subtracts the mean trace and constructs a second
traceless diagonal correction.  The determinant-one equation proves that the
two compact-real-form exponentials multiply to the original matrix.  Hence
every `SU(N)` element is a product of two such exponentials, which supplies the
exact finite-product generation object used by the integration bridge.

The new `SU2DifferentiatedExponentialAction` and
`SU3DifferentiatedExponentialAction` certificates isolate the
representation-dependent input to the single equation
`rho(exp X) = exp(d rho X)`.  At the global level,
the earlier `SU2SU3CompactExponentialLieTheory` interface is retained for
compatibility, but its exponential-surjectivity fields are no longer needed.
The sharper `SU2SU3DifferentiatedExponentialLieTheory` asks only for
construction of those compatible differentiated actions for each intended
finite-dimensional jointly continuous irrep.  Lean checks its conversion all
the way to the complete semisimple embedding classification weak-doublet branch conclusion, including in
`AuditEmbeddingClassification.lean`.

`GUT/SU6/Hypercharge/OneParameterSubgroup.lean` now proves that a multiplicative
one-parameter subgroup of a real Banach algebra is `t |-> exp(tD)` whenever
its derivative at zero is `D`.  `GUT/SU6/Embeddings/DifferentiatedRepresentationBridge.lean`
transports every abstract finite-dimensional representation to the canonical
normed coordinate space, proves that `t |-> rho(exp(tX))` satisfies the
multiplicative law, and transports the resulting time-one equation back to
`finiteDimensionalExponential`.  Consequently the new
`SU2SU3DerivativeAtIdentityLieTheory` does not assume
`rho(exp X) = exp(d rho X)`: Lean derives that equation and checks the complete
semisimple embedding classification weak-doublet branch conclusion from derivative-at-zero certificates.

The same bridge now uses a sharper intrinsic source certificate.  Every
traceless complex matrix is explicitly decomposed as `K + i S` with `K` and
`S` in the compact skew-adjoint real form, and Lean proves that this real form
complex-linearly spans all of `sl(n, Complex)`.  The compact real form itself
is now a checked real Lie algebra under the matrix commutator.  Lean proves
that every real Lie homomorphism from this compact form has an explicit
complex Lie-hom extension to `sl(n, Complex)`, that the extension preserves
brackets, and that it agrees with the original map on every compact
direction.  A `RealLieHomDerivativeAtIdentityAction` therefore accepts the
form of differential naturally produced by Lie-group differentiation and
constructs `LieHomDerivativeAtIdentityAction` internally.  The combined
`SU2SU3RealLieHomDerivativeTheory` is checked all the way through the complete
semisimple embedding classification weak-doublet branch theorem.

The differential bridge now also proves functoriality under actual invariant
subspaces.  From the operator derivative it derives the derivative of every
vector orbit; a finite-dimensional invariant subspace is closed, so its slope
limit remains in that subspace.  Orthogonal projection then transports the
operator-valued derivative to canonical coordinates on the subtype.  Thus
`RealLieHomDerivativeAtIdentityAction.restrictToSubrepresentation` constructs
the complete restricted real Lie-hom derivative certificate, including its
one-parameter derivative identity, without an extra smoothness assumption on
the constituent.

The Lie-homomorphism law of the ambient differential is no longer an
independent source assumption.  `GUT/SU6/Embeddings/SpecialUnitaryLieAlgebra.lean` equips
the compact real form with its induced finite-dimensional normed topology,
defines special-unitary conjugation on it, proves
`exp(t Ad_g Y) = g exp(tY) g^-1`, and computes the derivative of
`t |-> Ad_(exp(tX)) Y` as `[X,Y]`.  The new
`RealLinearDerivativeAtIdentityAction` asks only for a real-linear candidate
and its derivative identity along every compact one-parameter subgroup.
Differentiating the representation conjugation identity first in the
represented subgroup parameter and then in the conjugating parameter proves
equivariance and bracket preservation.  Lean then constructs the former
`RealLieHomDerivativeAtIdentityAction` internally.

`RealDifferentiableProductAction` consequently records only two certificates:
the real differentials of the ambient `SU(3)` and `SU(2)` restrictions of one
product representation.  Lean restricts these first to every constituent in
the unitary semisimple decomposition and then to the concrete color factor and
weak multiplicity range selected by product factorization.  The endpoint
`injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realDifferentiableProductAction`
therefore proves the full semisimple embedding classification branch conclusion from the two ambient
differentials of the actual six-dimensional defining restriction.  The new
chain is included in `AuditEmbeddingClassification.lean` and uses only `propext`,
`Classical.choice`, and `Quot.sound`.

More sharply, `RealLinearlyDifferentiableProductAction` records only the two
ambient real-linear differentials and their one-parameter derivative
identities.  Its checked conversion derives both Lie laws and reaches the
classified and numerical semisimple embedding classification weak-doublet endpoints through
`injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realLinearlyDifferentiableProductAction`
and
`injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realLinearlyDifferentiableProductAction`.
These endpoints are also included in `AuditEmbeddingClassification.lean`.

Those two ambient real-linear derivative certificates are no longer
independent source inputs once a differential of the matrix embedding itself
is available.  `GUT/SU6/Embeddings/EmbeddingDifferentialBridge.lean` defines
`OneParameterDifferentiableEmbedding`: one real-linear map
`su(3) x su(2) -> su(6)`, together with its derivative identity on every
product one-parameter subgroup.  Lean transports this matrix derivative to
the canonical Euclidean defining action, obtains the color and weak
certificates by restriction, and reaches both the classified and numerical semisimple embedding classification
endpoints.  These endpoint theorems are included in `AuditEmbeddingClassification.lean` and use
only `propext`, `Classical.choice`, and `Quot.sound`.

The matrix-level certificate is stable under an ambient change of basis.
`EmbeddingDifferentialBridge.OneParameterDifferentiableEmbedding.targetConjugate`
conjugates both the embedding and its compact-real differential and proves the
required derivative identity; the corresponding continuous embedding is
constructed by `conjugateContinuousEmbedding`.

The intended standard representative is now fully instantiated rather than
merely assumed.  `GUT/SU6/Embeddings/StandardSemisimpleEmbedding.lean` constructs the
injective continuous block homomorphism `(A,B) |-> diag(A,B,1)` and proves
directly that its differential is `(X,Y) |-> diag(X,Y,0)` by differentiating
the two matrix exponentials.  `GUT/SU6/Embeddings/StandardSemisimpleEmbeddingWitness.lean`
pairs this embedding with the actual continuous circle
`diag(z,z,z,z,z,z^-5)`, proves all 36 matrix entries of the commutation
relation, proves nontriviality at `z = -1`, and reaches the classified and
numerical semisimple embedding classification endpoints.  These concrete results and their axiom dependencies
are included in `AuditEmbeddingClassification.lean`.

`GUT/SU6/Embeddings/SmoothEmbeddingBridge.lean` now closes the source step for an explicit
ordinary first-order matrix-smooth scope.  For a homomorphism `iota`, it forms
the matrix-valued exponential-coordinate map
`(X,Y) |-> iota(exp X, exp Y)`.  From the standard mathlib hypothesis
`DifferentiableAt Real` at `(0,0)`, Lean extracts its Frechet derivative.
Differentiating the unitary identity proves that every derivative value is
skew-adjoint; differentiating determinant one, using the newly checked theorem
that the Frechet derivative of determinant at the identity is trace, proves
that it is traceless.  The derivative therefore corestricts automatically to
a real-linear map `su(3) x su(2) -> su(6)` and constructs the earlier
`OneParameterDifferentiableEmbedding` without assuming tangent-space,
bracket, or exponential-compatibility fields.

The same file supplies a second, convenient source interface for smooth or
matrix-algebraic constructions: an ambient matrix extension differentiable at
the identity and agreeing with the group map.  The checked Frechet derivative
of the source matrix exponential converts this interface to the exponential
coordinate hypothesis.  Both the classified and numerical semisimple embedding classification endpoints are
now proved directly from either source interface.

`GUT/SU6/Embeddings/StandardSmoothEmbeddingWitness.lean` instantiates the ambient
interface for the intended standard representative using its affine block
matrix extension and proves the resulting exponential-coordinate map is
differentiable.  Thus the source class is concrete and inhabited, rather than
an assumed Lie-action package.

`GUT/SU6/Embeddings/ContinuousEmbeddingRegularityBridge.lean` closes the remaining
continuity-only source step.  TauCeti's classification of continuous
one-parameter subgroups produces the canonical matrix generator of every
embedded exponential line.  Reparameterization proves real homogeneity, and
the matrix Trotter formula plus uniqueness of limits proves additivity.
Differentiating unitarity and determinant one shows that the generator is
skew-adjoint and traceless, so it corestricts to a real-linear map
`su(3) x su(2) -> su(6)`.  This constructs the previously required
`OneParameterDifferentiableEmbedding` certificate from continuity alone.  The
global exponential-coordinate identity also proves that the chart map is
Frechet differentiable at zero with this generator as derivative.

Consequently,
`continuousInjectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition`
and
`continuousInjectiveEmbedding_with_hypercharge_has_weakDoubletBranch` prove
the semisimple embedding classification conclusions directly for every continuous injective homomorphism with
a nontrivial commuting continuous circle.  `AuditEmbeddingClassification.lean` confirms that the
new chain uses only `propext`, `Classical.choice`, and `Quot.sound`.

It is no longer necessary to assume bracket preservation, differentiability,
or exponential compatibility at the source, nor to differentiate selected
irreducible factors separately.  An exact up-to-conjugacy/source-automorphism
classification of the full homomorphism still requires
representation-identification data beyond the decomposition and centralizer
conjugacy proved here.  That stronger statement is a lower-priority extension
and is not used by the scoped no-go argument.

---

## 6. Scope and limitations

**Scope boundary:** an earlier formulation claimed that the displayed block
embedding was the only weak-doublet-capable embedding up to conjugacy.  That
stronger claim is false without the commuting hypercharge hypothesis.  The
tensor-product homomorphism with defining restriction `6 = (3,2)` is faithful
and already contains weak doublets; the hypercharge hypothesis excludes it
because its commutant is scalar while scalar matrices in `SU(6)` form only the
finite center.  The remaining shape `(3,1)+(1,3)` kills `(1,-I_2)` and hence is
not an embedding of the direct product at group level.  Finally, `3` and
`3-bar` are related by an outer automorphism of the source `SU(3)`, not in
general by conjugacy inside `SU(6)`.  Any future classification of the full
homomorphism must therefore state both ambient conjugacy and the relevant
source automorphism explicitly.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
