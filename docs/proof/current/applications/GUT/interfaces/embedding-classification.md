# Semisimple embedding classification formalization

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The continuous
semisimple-embedding interfaces derive the dimension-six branch conclusions and
weak-doublet constraints in their stated scope.

## 2. Inputs And Conclusion

The source is an actual `SU(3) x SU(2) -> SU(6)` homomorphism; faithfulness,
commuting-circle and differentiated/highest-weight interfaces are retained where
required.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Complete reducibility, product factorization and low-dimensional highest weights
combine with weak-center and centralizer obstructions.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

- `GUT.AuditEmbeddingClassification`
  - keeps reproducible `#print axioms` checks for the principal semisimple embedding classification
    decomposition theorems and their highest-weight and semisimple-decomposition
    dependencies;
  - currently confirms that these declarations use only `propext`,
    `Classical.choice`, and `Quot.sound`, and do not depend on `sorryAx` or an
    additional project axiom.
- `GUT.ContinuousEmbeddingRegularityBridge`
  - applies TauCeti's classification of continuous one-parameter subgroups to
    each compact-real source exponential line of a continuous
    `SU(3) x SU(2) -> SU(6)` homomorphism;
  - proves real homogeneity by reparameterization and additivity from the
    matrix Trotter formula and uniqueness of limits;
  - differentiates the unitary and determinant-one identities to prove that
    the canonical generator is skew-adjoint and traceless, then packages it as
    a real-linear differential `su(3) x su(2) -> su(6)`;
  - constructs `OneParameterDifferentiableEmbedding` from continuity alone and
    proves both the classified and numerical semisimple embedding classification weak-doublet endpoints;
  - identifies the full exponential-coordinate map with the matrix exponential
    of the continuous linear generator, proving the stronger Frechet
    differentiability interface formerly assumed by the scoped assembly.
- `GUT.AuditHyperchargeCentralizer`
  - keeps reproducible axiom checks for the general Schur reduction, the
    concrete standard-block commutant, trace preservation under transport,
    the two-parameter traceless centralizer theorem, orthogonality of the
    actual constituents, both directions of the compact-centralizer
    coefficient equivalence, the transported circle cocharacter lattice,
    primitive-pair criterion, and concrete cocharacter matrix derivative;
  - currently reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `GUT.AuditCircleHomLattice`
  - keeps the covering-space proof that continuous circle endomorphisms are
    integer powers, and its two-torus consequence, under reproducible axiom
    audit;
  - currently reports only the standard logical/quotient axioms used by
    mathlib.
- `GUT.CompactEmbeddingClassification`
  - proves the unitary complete-reducibility part of semisimple embedding classification for every homomorphism
    `SU(3) x SU(2) -> SU(6)`, constructs the nontrivial weak-center element
    `(1,-I_2)`, and proves the resulting kernel obstruction to weak doublets;
  - specializes Schur's lemma to show an irreducible complex representation has
    scalar commutant and proves scalar `SU(6)` matrices have sixth-root scalar.
- `GUT.Burnside`, `GUT.ProductIrreducibility`, and
  `GUT.ProductFactorization`
  - prove finite-dimensional Burnside density over an algebraically closed
    field and use it to prove that external tensor products of irreducibles are
    irreducible;
  - construct the canonical multiplicity representation
    `Hom_G(rho, tau|G)`, prove evaluation is bijective, and prove the converse:
    irreducible product representations with semisimple factor restrictions
    factor as external tensor products of irreducibles;
  - realize the multiplicity factor as an equivalent invariant evaluation
    image in the ambient representation, so it can inherit the ambient
    topology.
- `GUT.CompactProductFactorization`
  - specializes product factorization to finite-dimensional unitary complex
    representations and packages both extracted factors as continuous
    finite-dimensional irreducibles;
  - packages real differentials on the two ambient factor restrictions and
    restricts them canonically to every invariant constituent, color factor,
    and concrete weak multiplicity range;
  - packages the still weaker pair of ambient real-linear identity
    differentials, derives their Lie laws through the differentiation bridge,
    and converts them to the existing factorization input;
  - under the one explicit highest-weight interface, derives the low color
    dimension list and exact weak-center sign for those factors.
- `GUT.ContinuousRepresentationScope`
  - records joint continuity of the group action, proves it is preserved by
    continuous restriction and invariant subspaces, and verifies it for the
    defining `SU(6)`, `SU(3)`, and `SU(2)` matrix representations;
  - isolates the remaining general highest-weight input as
    `SU2SU3HighestWeightTheory` and proves all semisimple embedding classification consequences needed from it;
  - provides the sharper `SU2LieSU3HighestWeightTheory`, where the `SU(2)`
    dimension formula is generated by the checked differentiated Lie model;
  - provides `SU2SU3GeneratedExponentialLieTheory`, where exponential
    generation and compatibility also derive the `SU(2)` center sign, and
    feeds it through the complete semisimple embedding classification branch theorem;
  - retains `SU2SU3CompactExponentialLieTheory`, whose source fields included
    concrete compact-exponential surjectivity and compatible differentiated
    actions;
  - provides `SU2SU3DifferentiatedExponentialLieTheory`, which removes the now
    proved group-generation input and checks that compatible differentiated
    actions alone imply the complete semisimple embedding classification branch conclusion;
  - provides `SU2SU3DerivativeAtIdentityLieTheory`, where compatibility with
    exponentials is no longer an input, and checks that identity-derivative
    certificates imply the complete semisimple embedding classification branch conclusion;
  - provides `SU2SU3LieHomDerivativeTheory`, whose source differential is a
    complex Lie homomorphism and whose induced Lie-module structures are
    constructed internally, and feeds it through the complete semisimple embedding classification branch
    theorem;
  - provides `SU2SU3RealLieHomDerivativeTheory`, whose source differential is
    only a real Lie homomorphism on the compact real form, complexifies it
    internally, and feeds it through the complete semisimple embedding classification branch theorem.
- `GUT.OneParameterSubgroup`
  - proves that the derivative at zero of a multiplicative real
    one-parameter subgroup determines its derivative at every time;
  - proves by a zero-derivative argument that a differentiable
    one-parameter subgroup in a real Banach algebra equals `exp(tD)`;
  - proves uniqueness of the derivative used to identify an intrinsic Lie
    differential on the compact real form.
- `GUT.DifferentiatedRepresentationBridge`
  - transports abstract finite-dimensional endomorphisms to continuous
    operators on mathlib's selected normed coordinate space;
  - identifies the transported `finiteDimensionalExponential` with the
    Banach-algebra exponential;
  - derives `rho(exp X) = exp(d rho X)` from the derivative at zero of each
    actual compact one-parameter action and packages the resulting `SU(2)`
    and `SU(3)` semisimple embedding classification certificates;
  - accepts the intrinsic differential as a complex Lie homomorphism,
    constructs the induced `LieRingModule` and `LieModule` instances, and
    proves uniqueness from compact-direction derivatives;
  - accepts instead the real Lie-hom differential naturally defined on
    `su(n)`, complexifies it internally, and preserves the supplied
    one-parameter derivative identities;
  - accepts more sharply a merely real-linear identity differential, derives
    conjugation equivariance from the represented conjugation identity, then
    differentiates once more to prove bracket preservation and construct the
    real Lie-hom differential internally;
  - proves that such a differential preserves every finite-dimensional group
    subrepresentation and constructs the complete derivative certificate on
    the subtype by transporting operator derivatives through orthogonal
    projection.
- `GUT.ExponentialRepresentationBridge`
  - proves that an invariant subspace of a finite-dimensional complex
    endomorphism is invariant under its operator exponential;
  - proves that an exponential acts on an eigenvector by the exponential of
    its eigenvalue, including for the chosen-basis finite-dimensional operator
    exponential;
  - proves that invariance and identity action on a generator family extend
    over all finite products, then derives Lie-submodule stability and
    zero-differential triviality from exponential compatibility;
  - packages the result without imposing a topology on the represented vector
    space by transporting the operator exponential through a finite basis.
- `GUT.HighestWeightBridge`
  - connects irreducible group actions to the checked `sl2` and `sl3`
    highest-weight classifications through differentiated Lie actions;
  - derives the `SU(2)` center eigenvalue `(-1)^n` from compatibility with the
    distinguished `pi*i*H` exponential instead of accepting that sign as an
    independent classification field.
- `GUT.SpecialUnitaryExponential`
  - computes the concrete matrix exponential of `pi*i*H` and proves that it is
    the nontrivial center element `-I_2` of `SU(2)`.
- `GUT.MatrixDeterminantExponential`
  - proves `det(exp A) = exp(trace A)` for every finite complex matrix by a
    checked complex-derivative argument.
- `GUT.SpecialUnitaryLieAlgebra`
  - defines the compact real form as traceless skew-adjoint matrices and proves
    that matrix exponential maps it into `SU(n)`;
  - equips that compact real form with its real vector-space and real Lie
    algebra structures and packages its inclusion into the scalar restriction
    of `sl(n, Complex)` as a real Lie homomorphism;
  - explicitly decomposes every traceless complex matrix into compact
    skew-adjoint parts and proves that the compact real form complex-linearly
    spans the full special linear Lie algebra;
  - explicitly extends every real-linear map from the compact form to a
    complex-linear map on `sl(n, Complex)`, and proves that a real Lie
    homomorphism extends to a complex Lie homomorphism agreeing on compact
    directions;
  - proves an extensionality theorem for complex-linear maps out of the
    special linear Lie algebra from equality on compact directions;
  - defines real scaling in the compact real form and proves that
    `t |-> exp(tX)` is a multiplicative one-parameter subgroup;
  - equips the compact real form with its induced finite-dimensional normed
    topology, defines its special-unitary adjoint action, proves exponential
    compatibility with conjugation, and computes the derivative of the
    adjoint exponential curve as the matrix commutator;
  - realizes the distinguished `SU(2)` center parameter in that concrete real
    form and derives finite-product generation from exponential surjectivity;
  - packages the remaining representation input as differentiated-action
    certificates containing precisely `rho(exp X) = exp(d rho X)`.
- `GUT.SpecialUnitaryGeneration`
  - extends the finite-dimensional unitary CFC logarithm across the possible
    `-1` spectral value, using finiteness of the matrix spectrum;
  - centers that logarithm and constructs a traceless diagonal phase
    correction, proving every element of nonzero finite `SU(n)` is a product
    of two compact-real-form exponentials;
  - supplies the exact finite-product generation certificates used for
    `SU(2)` and `SU(3)`; together with the one-parameter subgroup bridge this
    leaves construction and identification of the identity derivative as the
    sharpest semisimple embedding classification source input.
- `GUT.Sl2String`
  - proves that the finite lowering string of a primitive vector is linearly
    independent and stable under an `sl2` triple;
  - proves that irreducibility makes this string a basis, giving
    `finrank = highestWeight + 1`, and combines this with mathlib's primitive
    vector theorem to produce an integral highest weight.
- `GUT.StandardSl2`
  - constructs the standard `H`, `E`, and `F` inside the trace-zero
    two-by-two complex matrix Lie algebra and checks all `sl2` relations;
  - proves that this triple spans the whole algebra and that every
    one-dimensional module over it has zero Lie action.
- `GUT.FiniteSemisimpleDecomposition`
  - extracts a finite direct sum of simple constituents from a finite
    semisimple group-algebra module;
  - packages the module decomposition as a `Representation.Equiv` from the
    original representation to the dependent direct sum of its actual blocks;
  - transports continuity to every constituent, sums their dimensions, and
    reassembles constituent-wise identity actions on the ambient space.
- `GUT.WeakDoubletEmbeddingClassification`
  - turns the actual semisimple defining restriction into the certified finite
    block list under the explicit highest-weight interface;
  - excludes the weak-triplet branch by faithfulness at `(1,-I_2)` and the
    tensor-product branch by a nontrivial commuting continuous hypercharge
    circle, leaving the standard weak-doublet branch;
  - retains the actual classified constituents in the weak-doublet result and
    proves that their labels are exactly one `color3`, one `weak2`, and one
    `singlet`, hence that the semisimple decomposition has exactly three
    uniquely labelled blocks;
  - derives all constituent and product-factor derivative certificates from
    only the two ambient real differentials of the six-dimensional defining
    restriction; conjugacy of embeddings is still a separate geometric
    theorem.
- `GUT.ContinuousCentralizer`
  - proves that every continuous hypercharge circle commuting with an
    irreducible defining restriction is trivial, using Schur's lemma, the
    finite sixth roots of unity, and connectedness of `Circle`.
- `GUT.LowDimensionalConcreteIrreps`
  - constructs the defining color triplet, proves its irreducibility directly
    from explicit `SU(3)` elements, verifies continuity, and supplies concrete
    defining highest-weight certificates alongside the weak doublet.
- `GUT.LowDimensionalIrreps`
  - proves the dimension-six arithmetic of the `SU(3)` and `SU(2)` highest
    weight formulas and enumerates every product-block dimension at most six;
  - constructs branch counts only from a block list carrying explicit
    dimension-six and nontrivial-factor certificates, then invokes the checked
    three-branch classification.

## 6. Scope And Limitations

Compatibility input packages below are not all unconditional classification
theorems; geometric conjugacy is a separate conclusion.

## 7. Sources And Verification

The [scope dossier](../../../inputs/Math/EMBEDDING_CLASSIFICATION.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
