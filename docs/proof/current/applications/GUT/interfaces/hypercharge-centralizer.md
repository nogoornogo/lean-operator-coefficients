# Hypercharge centralizer and cocharacter formalization

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../../README.md).

## 1. Result And Status

Declaration map for the established interfaces below. The specified block
centralizer has explicit scalar coordinates, compact group equivalences and an
integral cocharacter classification.

## 2. Inputs And Conclusion

The actual `3+2+1` constituent decomposition and the stated irreducibility,
continuity and injectivity premises are kept explicit.

## 3. Definitions And Conventions

Module paths locate source files; retained `GUT.*` namespaces are compatibility
names, not directory assignments. Duals, signs, coordinate order and action
conventions are those of the named declarations and their displayed formulas;
no convention is changed by this catalogue.

## 4. Proof Structure

Schur reduction extracts block scalars; determinant and unitarity equations give
the compact coefficients; circle lifts give the integer lattice.

## 5. Lean Entry Points

The catalogue below retains public names, adapters and detailed interface
qualifications. Source declarations, rather than this map, fix elaborated types.

- `GUT.HyperchargeCentralizer`
  - proves the hypercharge centralizer geometry linear-algebra statement that traceless generators constant
    on the `3+2+1` blocks are uniquely `a*Y5+b*X`, with explicit inverse
    coefficients.
- `GUT.BlockCentralizer`
  - proves that the full commutant of three pairwise dimension-distinct
    irreducibles is block-scalar, then instantiates the concrete standard
    color, weak, and singlet blocks;
  - computes the trace, proves the unique complexified `a*Y5+b*X`
    parameterization, and gives an explicit equivalence
    `TracelessCommutant ≃ ℂ x ℂ`;
  - proves trace-preserving transport across a supplied representation
    equivalence, isolating the remaining geometric input.
- `GUT.ActualBlockCentralizer`
  - evaluates the semisimple embedding classification dependent direct sum at its three unique semantic
    constituent indices and proves this is an equivalence with the ordered
    actual `3+2+1` product representation;
  - applies the generic Schur theorem to these actual irreducible spaces,
    computes the trace as `3c+2w+s`, and proves unique complex `Y5/X`
    coefficients for every traceless commutant endomorphism;
  - composes this result with the injective-embedding and nontrivial commuting
    hypercharge-circle hypotheses from semisimple embedding classification.
- `GUT.CompactBlockCentralizer`
  - defines the determinant-one unit-circle coefficient group
    `c^3*w^2*s=1` for the actual `3+2+1` blocks;
  - proves by explicit mutually inverse maps that it is continuously
    group-equivalent to `Circle x Circle`.
- `GUT.UnitarySubrepresentationOrthogonality`
  - proves that orthogonal projection onto an invariant subspace intertwines a
    unitary representation;
  - combines this with Schur's lemma to prove orthogonality of irreducible
    invariant subspaces of unequal dimensions, and supplies range irreducibility
    and finrank lemmas for injective intertwiners.
- `GUT.ActualCompactCentralizer`
  - extracts the unique three scalar coefficients of every actual `SU(6)`
    centralizer element and proves they lie on the unit circle and obey the
    special-unitary determinant equation;
  - packages extraction as an injective homomorphism into the compact
    determinant-one coefficient group.
- `GUT.ActualCompactCentralizerEquivalence`
  - reconstructs a unitary operator on the original Euclidean representation
    from every compact coefficient triple, using the checked orthogonality of
    the three actual constituent ranges;
  - checks its standard-basis matrix is special unitary and centralizes the
    embedded semisimple image, then proves exact coefficient recovery;
  - concludes that the actual physical centralizer is abstractly
    group-equivalent to the coefficient group and hence to `Circle x Circle`.
- `GUT.ActualSkewCentralizer`
  - proves that block eigenvalues of a skew-adjoint actual commutant element
    are purely imaginary and hence that its complex `Y5/X` coefficients are
    uniquely `i*a` and `i*b` for real `a,b`;
  - proves the converse directly on the original Euclidean representation:
    every real `i*(a*Y5+b*X)` combination is skew-adjoint and trace-zero;
  - packages the anti-Hermitian trace-zero actual commutant as an explicit
    equivalence with `Real x Real`.
- `GUT.ActualCompactCentralizerTopology`
  - proves continuity of coefficient reconstruction by reducing every matrix
    entry to continuous scalar multiplication followed by a fixed
    finite-dimensional coordinate functional;
  - packages reconstruction as a continuous group equivalence with the
    determinant-one coefficient group and hence proves that the actual
    physical centralizer is topologically group-equivalent to
    `Circle x Circle`.
- `GUT.CircleHomLattice`
  - lifts each continuous circle endomorphism through `Circle.exp`, proves the
    lift is additive and real-linear, and forces its slope to be a unique
    integer using the period `2*pi`;
  - classifies continuous homomorphisms from `Circle` to `Circle x Circle` by
    a unique pair in `Integer x Integer`;
  - proves such a circle is injective exactly when the exponent pair is
    primitive.
- `GUT.ActualCompactCentralizerLattice`
  - transports the integer-pair classification to continuous circle
    homomorphisms into the actual physical `SU(6)` centralizer;
  - proves their three actual block exponents are
    `(m,n,-(3m+2n))` and computes the associated algebraic `Y5/X` coordinates
    `((n-m)/5,(3m+2n)/5)`;
  - transports the primitive-pair criterion to actual physical-centralizer
    circle embeddings.
- `GUT.CircleHomTangent`
  - proves directly that the coefficient curve `t |-> exp(t)^n` has real
    derivative `i*n` at the identity.
- `GUT.ActualCentralizerTangent`
  - differentiates every integer physical cocharacter on the actual defining
    representation and identifies its derivative with the checked
    anti-Hermitian `Y5/X` generator;
  - proves its standard-basis matrix curve is the underlying matrix of the
    actual `SU(6)` centralizer element and differentiates that matrix curve;
  - combines this with lattice uniqueness for an arbitrary continuous
    physical-centralizer cocharacter.
- `GUT.HyperchargeBranchArithmetic`
  - classifies primitive physical-centralizer cocharacters with a neutral
    defining block and proves that weak neutrality gives the flipped pair,
    while singlet neutrality gives the standard pair, in each case up to
    circle orientation;
  - proves the oriented two-branch conclusion for an injective actual physical
    circle from an oriented neutral block once the distinct primitive
    color-neutral pair is excluded.

## 6. Scope And Limitations

Primitive/cocharacter and branch conclusions use their stated neutral-block and
orientation premises, not arbitrary embedding classification.

## 7. Sources And Verification

The [scope dossier](../../../inputs/Math/HYPERCHARGE_CENTRALIZER.md) supplies related statement and hypothesis context;
internal document links are navigation, not quotations or extra theorem inputs.
Library API references identify proof dependencies, not unproved premises,
except for the explicit literature boundary where stated.

Build counts and warning reports retained below describe their original
checkpoints, not a new build baseline. Commands assume `elan`, `lake` and
`lean` on PATH and execution from the repository root. This formatting pass
changes no Lean source or dependency pin and reruns no Lean build.
See the [documentation topic](../../../../TEMPLATE.md)
for this pass's checks.
