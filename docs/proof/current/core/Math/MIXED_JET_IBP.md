# Internal Linear Actions And Mixed Jet IBP

## Source And Convention

For component types `F,B` and a direction type `I`, the jet modules are free
complex modules on `F × (I →₀ ℕ)` and `B × (I →₀ ℕ)`. A specified field basis
fixes this presentation; a field representation may mix its components by
arbitrary linear maps. No finite-dimensionality assumption is needed for the
construction. Finite components and directions enter the finite-grade result.

The actual mixed algebra is

$$
A=\Lambda(J_F)\otimes\mathbb C[X_{b,\alpha}].
$$

All odd components and their jets belong to one exterior algebra, including
cross-component signs. `JetLinear.polynomialEquiv` identifies the even free
symmetric algebra with this polynomial presentation. It intertwines the lifted
field maps and actual derivatives; both presentation directions are available.
Generators are source vectors, and coefficients are linear maps on the source.

The jet tower is unbounded, with ordinary derivative symbols and no factorial
or momentum normalization. `D_i` shifts a generator's multi-index by `e_i`.
On the actual tensor algebra it is the sum of the two factor derivatives.
It is **even**:

$$
D_i(pq)=(D_i p)q+p(D_i q).
$$

The generator rules, this Leibniz rule and pairwise commutation are proved.
The exterior factor uses Physlib's proved even derivation; the polynomial
factor uses the existing Mathlib scalar derivation. Odd Grassmann contractions
are used only as coordinate probes in the concrete example, not as `D_i`.

## Joint Subspaces And The Existing Coefficient Source

`grade F B I n m d` is the span, inside the actual algebra, of products with
`n` odd generators, `m` even generators and total derivative order `d`.
Multiplication adds all three counts, and each derivative raises only `d`.
These are actual homogeneous subspaces; the package does not assert a new
global direct-sum decomposition theorem for the whole mixed algebra.

For finite `F,B,I`, every fixed grade is finite-dimensional. A generator in
a spanning word has order at most `d`; finitely many bounded multi-indices
and component labels therefore give a finite spanning family. Higher jets
are not killed or identified by that argument.

The existing statistics-constrained source is

$$
S_{n,m}=\Lambda^n J_F\otimes\mathrm{Sym}^m J_B.
$$

`MixedJetSource.embed` maps its exterior factor into the exterior algebra and
its symmetric factor into homogeneous polynomials. The latter uses a proved
basis equivalence, `SymmetricPolynomialPower.equiv`, with the expected product
formula on arbitrary vectors. The tensor map is injective, and its evaluation
on pure basis tensors is exactly the spanning word in the actual algebra.
`sourceEquiv` identifies the full source with its image at fixed field counts.

Pulling back a derivative grade gives `sourceGrade`; `gradeEquiv` identifies it
with the entire actual grade, in both directions. `coefficientEquiv` transports
linear coefficient maps inversely and has evaluation formulas. The embedding,
grade equivalence and restricted representations are equivariant for the actual
exterior/symmetric-power actions. These are proved source bridges rather than
a presumed coefficient matrix or a supplied completeness premise.

At `d=0`, `MixedJetSource.zeroEquiv` recovers the existing derivative-free source

$$
\Lambda^n\mathbb C^{(F)}\otimes\mathrm{Sym}^m\mathbb C^{(B)}.
$$

Its inverse is proved using the zero-order inclusion and a retraction. The
range is exactly the zero-derivative grade; positivity of multi-index order
rules out every higher jet in a spanning word of that grade.
`zeroRepresentationEquiv` also preserves the given internal actions.

## Internal Actions And IBP Descent

Arbitrary group representations on the two component modules act fibrewise
at each derivative multi-index. These actions fix directions, preserve joint
grades and commute with the actual total derivatives. The scalar construction
also extends the earlier component-permutation wrappers: `JetLinear.shear`
gives an invertible non-permutation control at every jet order.

For a target with positive derivative count, currents and relations are

$$
J_{n,m,d}=\bigoplus_{i\in I}A_{n,m,d},\qquad
\mathrm{div}(j)=\sum_i D_i j_i,\qquad
R_{n,m,d}=\mathrm{im}(\mathrm{div})\subset A_{n,m,d+1}.
$$

Currents have finite support. The annihilator criterion is exactly
`f(R)=0 ↔ ∀ i p, f(D_i p)=0`. Covariance proves relation stability, and the
existing `RelationQuotient` construction supplies inverse coefficient descent.
For homogeneous products the formal IBP statement is
`f(p D_i q) = -f((D_i p) q)`. Reordering odd factors is a separate statistics
operation; no reordering sign is inserted into the even Leibniz rule.

For commuting local and residual component actions, `localEquiv` identifies
local-invariant, relation-annihilating coefficients with residual-equivariant
maps on local coinvariants modulo the image of actual divergences.
The shared `GradedJetIBP` interface proves forward/inverse evaluation and
zero/nonzero criteria; `MixedJetIBP` instantiates it with the proved actual
derivatives and covariance. No finite-group, averaging, semisimplicity or
invariant-exactness premise is required. The IBP range is a linear submodule,
not an ideal of the full algebra.

## Complete Mixed Consumer

Take one odd component `ψ`, one even component `φ` and one direction. Write
subscripts for derivative orders. The entire grade `(nF,nB,d)=(2,1,2)` is spanned by

$$
A=\phi_1\psi_0\psi_1,\qquad B=\phi_0\psi_0\psi_2.
$$

The full preceding grade is spanned by `P=φ₀ψ₀ψ₁`. Actual differentiation gives

$$
DP=\phi_1\psi_0\psi_1+\phi_0\psi_1^2+\phi_0\psi_0\psi_2=A+B,
\qquad R_{2,1,1}=\mathbb C(A+B).
$$

The middle term vanishes in the exterior algebra. Full source/current spans
are proved by classifying all nonnegative order triples of total two/one,
including repeated odd generators and the negative reordered terms.

Two explicit exterior contractions and polynomial coefficient extraction give
the linear reduction `a A + b B ↦ a-b`. Its kernel is exactly the divergence
range and it is surjective. `quotientEquiv` therefore identifies the actual
quotient with ℂ, `quotient_finrank` proves dimension one, `first_survives`
proves `[A]≠0`, and `ibp_identity` proves `[B]=-[A]`.

## Entry Points And Verification

- [JetLinear](../../../../../Math/Algebra/Jets/JetLinear.lean) and
  [scalar linear IBP](../../../../../Math/RepresentationTheory/Constructions/ScalarLinearIBP.lean).
- [Mixed algebra](../../../../../Math/Algebra/Jets/MixedJetAlgebra.lean),
  [grades](../../../../../Math/Algebra/Jets/MixedJetGrading.lean),
  [finite grades](../../../../../Math/Algebra/Jets/MixedJetFinite.lean) and
  [internal actions](../../../../../Math/RepresentationTheory/Jets/MixedJetAction.lean).
- [Symmetric-power polynomial bridge](../../../../../Math/LinearAlgebra/Symmetric/SymmetricPolynomialPower.lean),
  [mixed source bridge](../../../../../Math/RepresentationTheory/Jets/MixedJetSource.lean) and
  [derivative-free boundary](../../../../../Math/RepresentationTheory/Jets/MixedJetZero.lean).
- [Actual mixed IBP](../../../../../Math/RepresentationTheory/Jets/MixedJetIBP.lean) and
  [shared graded descent](../../../../../Math/RepresentationTheory/Jets/GradedJetIBP.lean).
- [Complete consumer](../../../../../Math/Algebra/Jets/MixedJetQuadratic.lean),
  [coordinate probes](../../../../../Math/Algebra/Jets/MixedJetPairCoordinates.lean) and
  [strict audit](../../../../../Math/Algebra/Jets/Audit/AuditMixedJetIBP.lean).
- [Contract](../../../../topics/derivative-ibp/mixed-implementation-plan.md),
  [source register](../../../../topics/derivative-ibp/references.md) and
  [verification](../../../../topics/derivative-ibp/verification.md).

The new audit checks 223 declarations transitively, permits only the standard
axioms and rejects Physics/GUT imports. Full `lake build` passes 7594 jobs.
Dependency pins and recursion/kernel limits are unchanged. Explicit carrier
types, local reducible additive/module instances and factorwise equalities
avoid expensive inference through tensor/submodule presentations.

Direction mixing, actual Lorentz transformations, gauge-covariant derivatives,
EOM/Bianchi relations, analytic integrated actions, amplitude equivalence,
momentum comparison and general EFT enumeration remain outside this result.
No literature counting theorem or physical application premise is imported.

The subsequent [direction/EOM extension](DIRECTIONAL_JET_EOM_IBP.md) lifts
direction-mixing actions to this actual mixed source. Its
[Lorentz specialization](../Physics/LORENTZ_SCALAR_EOM_IBP.md) checks scalar
contractions and Weyl transformations; its EOM construction is scalar. The
A/B baseline and its own boundaries above remain unchanged.

The later [scalar inclusion](../../../../../Math/Algebra/Constructions/MixedScalarInclusion.lean)
embeds the scalar polynomial source as the even factor, commutes with total
derivatives and intertwines arbitrary supplied jet actions. It transports
the complete scalar two-sided differential equation closure when the seed
images belong to the target closure. Its
[strict audit](../../../../../Math/Algebra/Constructions/Audit/AuditMixedScalarInclusion.lean)
retains Math-layer imports and standard axioms. This is an inclusion and
relation transport result, without an equality of arbitrary scalar/mixed
relation preimages or a mixed invariant-basis claim.
