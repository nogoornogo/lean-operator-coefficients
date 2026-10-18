# Hypercharge centralizer geometry

Historical independent result: retained for provenance and reuse, not a premise
of the current graded operator completeness claim. See the [role index](../../../README.md).

See the [proof-document conventions](../../../TEMPLATE.md) for citation roles and build prerequisites.

## 1. Result and status

The broader [multiplicity-centralizer generalization](MULTIPLICITY_CENTRALIZER.md)
now covers algebraic commutants and GL centralizers with repeated constituents.
Its general U/SU source bridge is still open. The concrete `3+2+1` compact
centralizer and topology proved in this dossier are preserved.

## 2. Inputs and conclusion

For the surviving semisimple embedding, hypercharge lies in the rank-2 centralizer torus and may be written symbolically as

\[
Y=aY_5+bX.
\]

## 4. Proof structure

### Centralizer and cocharacter lattice

#### Status

`LEAN-CHECKED FOR THE CLASSIFIED EMBEDDING AT THE COMPLEXIFIED-COMMUTANT, TOPOLOGICAL TWO-TORUS, ANTI-HERMITIAN REAL-FORM, COCHARACTER-LATTICE, AND CONCRETE MATRIX-TANGENT LEVELS`

**Lean update:** `GUT/SU6/Hypercharge/HyperchargeCentralizer.lean` models a block-scalar
infinitesimal centralizer generator by rational coefficients `(c,w,s)` with
`3c+2w+s=0`.  Lean proves that
`Y5=(-2,3,0)` and `X=(1,1,-5)` give a unique parameterization of this space,
including an explicit equivalence with `ℚ x ℚ`.

`GUT/SU6/Hypercharge/BlockCentralizer.lean` now proves the missing Schur/intertwiner
statement.  It shows generally that intertwiners between irreducibles of
different finite dimensions vanish, constructs the concrete color-triplet,
weak-doublet, and singlet representations of `SU(3) x SU(2)`, and proves that
the full commutant of their `3+2+1` sum is block-scalar.  Lean computes its
trace as `3c+2w+s`, proves existence and uniqueness of the complexified
`a*Y5+b*X` coefficients, and packages the traceless commutant as an explicit
equivalence with `ℂ x ℂ`.  Rational generators from
`HyperchargeCentralizer` map to traceless commuting endomorphisms.

The same file proves that commutants and trace transport across a supplied
representation equivalence.  `GUT/SU6/Hypercharge/ActualBlockCentralizer.lean` completes
that transport for the actual semisimple embedding classification decomposition: evaluation at the three
unique constituent indices is proved bijective using an explicit
`DFinsupp.single` inverse, and it intertwines the dependent direct sum with an
ordered `3+2+1` product of the actual irreducible spaces.  The generic Schur
theorem then proves that every actual commutant endomorphism is block-scalar,
computes the trace as `3c+2w+s`, and gives every traceless element unique
complex `Y5/X` coefficients.  This is also composed with the physical semisimple embedding classification
embedding and hypercharge-circle hypotheses.

`Math/RepresentationTheory/Unitary/UnitarySubrepresentationOrthogonality.lean` proves the geometric
input that was missing from the arbitrary decomposition equivalence: ranges
of inequivalent finite-dimensional irreducible subrepresentations of a
unitary representation are orthogonal when their dimensions differ.  The
proof makes orthogonal projection an intertwiner and applies Schur's lemma.

`GUT/SU6/Hypercharge/CompactBlockCentralizer.lean` defines the determinant-one coefficient
group
`{(c,w,s) in Circle^3 | c^3*w^2*s=1}` and gives an explicit continuous group
equivalence with `Circle x Circle`.  `GUT/SU6/Hypercharge/ActualCompactCentralizer.lean`
extracts these coefficients from every actual `SU(6)` centralizer element,
proves their unit norms and determinant equation, and proves that extraction
is injective.  `GUT/SU6/Hypercharge/ActualCompactCentralizerEquivalence.lean` constructs
the converse: it scales the three actual orthogonal constituents, proves that
the conjugated action preserves the Euclidean inner product, forms its matrix,
checks unitarity and determinant one, and proves that the matrix centralizes
the embedding.  Coefficient recovery is exact, so Lean now gives an abstract
group equivalence between the actual centralizer and `Circle x Circle`.

`GUT/SU6/Hypercharge/ActualSkewCentralizer.lean` now identifies the infinitesimally
unitary real form.  Lean proves that a nonzero eigenvector of a skew-adjoint
operator has purely imaginary eigenvalue, applies this to the actual color
and weak constituent ranges, and deduces that both complex `Y5/X`
coefficients of a skew-adjoint trace-zero commutant element are uniquely of
the form `i*a` and `i*b` with `a,b` real.  Conversely, orthogonality of the
actual constituent ranges proves directly that every such real combination
is skew-adjoint and trace-zero.  The resulting real form is explicitly
equivalent to `Real x Real`.

`GUT/SU6/Hypercharge/ActualCompactCentralizerTopology.lean` upgrades the group result to
the actual topology.  It proves continuity of matrix reconstruction entry by
entry using finite-dimensional coordinate functionals, packages
reconstruction as a group homomorphism, and uses the compact-to-Hausdorff
inverse theorem to prove coefficient extraction continuous.  Consequently
the physical matrix centralizer is now explicitly `ContinuousMulEquiv` to
`Circle x Circle`.

`Math/LieGroups/Torus/CircleHomLattice.lean` proves directly that every continuous circle
endomorphism is a unique integer power map.  It uses the existing
covering-space lift theorem for `Circle.exp`, proves the lift additive by
uniqueness, invokes the existing theorem that a continuous additive map
`Real -> Real` is real-linear, and uses periodicity to force an integer slope.
Coordinatewise, continuous homomorphisms `Circle -> Circle x Circle` are
therefore classified by `Integer x Integer`.

`GUT/SU6/Hypercharge/ActualCompactCentralizerLattice.lean` transports this classification
through the checked actual-centralizer `ContinuousMulEquiv`.  Thus every
continuous circle homomorphism into the physical matrix centralizer has a
unique integer pair `(m,n)`, with actual color, weak, and singlet block phases
`z^m`, `z^n`, and `z^(-(3m+2n))`.  Lean also verifies algebraically that the
corresponding real `Y5/X` coordinates are
`((n-m)/5,(3m+2n)/5)` and recover those three slopes.

The same lattice file proves that a physical centralizer circle is injective
exactly when its exponent pair is primitive, `gcd(m,n)=1`.
`Math/LieGroups/Torus/CircleHomTangent.lean` differentiates each integer power coefficient
along `Circle.exp` and obtains the exact slope `i*n`.
`GUT/SU6/Hypercharge/ActualCentralizerTangent.lean` then differentiates the action on the
actual defining representation, identifies the result with the checked
anti-Hermitian `Y5/X` element at coordinates
`((n-m)/5,(3m+2n)/5)`, and upgrades this pointwise statement to the actual
standard-basis `SU(6)` matrix curve.  Finally, every arbitrary continuous
circle homomorphism into the physical centralizer is assigned its unique
integer pair together with this matrix derivative.

Thus the hypercharge centralizer geometry differential bridge needed here is checked concretely in the
ambient matrix normed space.  The project has not introduced a separate
smooth-manifold structure on the subgroup and identified an abstract tangent
bundle with this matrix model; that would be optional Lie-group packaging,
not an unproved step in the stated matrix-level classification.

## 7. Sources and verification

Reference roles: linked Lean files are implementation or audit evidence; linked repository documents provide supplementary context, not external theorem premises. Any literature input is identified explicitly below or in the linked boundary dossier. Recorded build and audit outcomes are historical checkpoints; this documentation revision did not rerun Lean.
