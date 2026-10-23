# Scalar Jets And Formal IBP Coefficients

## Source And Derivatives

The scalar foundation uses the actual polynomial algebra

$$
A=\mathbb C[X_{a,\alpha}],\qquad
\alpha\in\mathbb N^{(I)},\qquad
D_iX_{a,\alpha}=X_{a,\alpha+e_i}.
$$

Scalar-component labels and derivative directions are arbitrary types.
Every expression has finite support, but the set of jet orders is unbounded.
The convention is ordinary derivatives, with no Taylor factorial or momentum
phase. The algebra is commutative and off shell. `totalDerivative` is the
Mathlib derivation constructed from these generator values. Its generator
formula, Leibniz rule and pairwise commutation are proved.

Give a generator weight `(1, |alpha|)`, where `|alpha|` is its total multi-index
order. The homogeneous submodule `grade n d` has field count `n` and total
derivative count `d`. The restricted derivative is a linear map

$$
D_i:A_{n,d}\longrightarrow A_{n,d+1}.
$$

For finite component and direction types, every fixed grade is
finite-dimensional. The proof bounds each monomial exponent by `n` and the
order of every occurring jet by `d`, then embeds the possible exponent vectors
into functions from a finite jet set to `Fin (n+1)`. This is a finiteness proof
inside the unbounded algebra; higher derivatives are never set to zero.

## Actual Divergences And Coefficient Convention

At positive derivative degree define the current space and divergence by

$$
J_{n,d}=\bigoplus_{i\in I}A_{n,d},\qquad
\mathrm{div}(j)=\sum_i D_i j_i,
\qquad R_{n,d}=\mathrm{im}(\mathrm{div})\subset A_{n,d+1}.
$$

The direct sum is implemented by finitely supported currents. The formal IBP
operator space is `A_(n,d+1) / R_(n,d)`. The relation submodule is constructed
from the actual derivatives; it is not a supplied relation matrix, a presumed
complete list, or an ideal of the full polynomial algebra.

Coefficients here are linear functionals on the operator source. They descend
to the quotient exactly when they vanish on every divergence. The proved
generator criterion is

$$
R_{n,d}\subset\ker f
\quad\Longleftrightarrow\quad
f(D_i p)=0\quad\hbox{for every }i\in I,\ p\in A_{n,d}.
$$

For homogeneous `p,q`, the proved graded product formula gives the usual formal
IBP identity `f(p D_i q) = -f(q D_i p)` in the common target grade. This is a
linear-functional statement on formal jets, without an analytic integration
or boundary premise.

## Symmetries And Existing Hom Descent

A group homomorphism `r : H → Perm S` acts by relabelling scalar components
and fixing derivative directions. This action preserves both grades and
commutes with all total derivatives. Divergence is covariant and its range
is stable. `coefficientEquiv` constructs the inverse linear correspondence

$$
\{f\in\mathrm{Hom}_H(A_{n,d+1},\mathbb C):f(R_{n,d})=0\}
\simeq
\mathrm{Hom}_H(A_{n,d+1}/R_{n,d},\mathbb C).
$$

Both directions have evaluation formulas on quotient classes. For another
component action `a : G → Perm S` commuting pointwise with `r`, `localEquiv`
additionally imposes local invariance using `LocalRelationHom`: take the local
coinvariants and then quotient by the image of the actual divergences.
The result is an exact residual-Hom correspondence, with zero/nonzero
equivalences. No invariant complement, averaging, compactness, finite group,
semisimplicity or exchange of invariants with a quotient is assumed.

The concrete symmetry construction covers component permutations fixing
directions. Arbitrary linear mixing of components and spacetime mixing of
directions are not claimed by these wrappers. The underlying generic descent
interfaces retain their arbitrary supplied representations. Existing
derivative-free exterior/symmetric completeness statements are unchanged.

## Complete Quadratic Consumer

For one scalar, one direction, two fields and two derivatives, write `X_k`
for the jet of order `k`. The complete source is spanned by

$$
A=X_1^2,\qquad B=X_0X_2.
$$

The entire preceding-grade current component is spanned by `X_0X_1`.
Ordinary differentiation proves

$$
D(X_0X_1)=A+B,
\qquad R_{2,1}=\mathbb C(A+B).
$$

The source and primitive reconstruction theorems classify all monomial
supports of those grades, including all possible orders of the unbounded jet
algebra. They are not checks of a selected candidate list alone.
The linear map `a A + b B ↦ a-b` is surjective and has exactly this divergence
range as its kernel. It induces an explicit quotient equivalence with
`C`, proves quotient dimension one, proves `[A]` survives and proves
`[B]=-[A]`. No equation `X_2=0` or other EOM is imposed.

## Entry Points, Provenance And Limits

- [ScalarJetAlgebra](../../../../../Math/Algebra/Jets/ScalarJetAlgebra.lean):
  jet indexing, derivations, commutation and grade shift.
- [ScalarJetGrading](../../../../../Math/Algebra/Jets/ScalarJetGrading.lean):
  covariance, finite grades and graded product maps.
- [ScalarJetIBP](../../../../../Math/RepresentationTheory/Jets/ScalarJetIBP.lean):
  divergence range, annihilator criterion, formal IBP and coefficient/Hom descent.
- [ScalarJetQuadratic](../../../../../Math/Algebra/Jets/ScalarJetQuadratic.lean):
  complete concrete source, relation and quotient consumer.
- [Strict audit](../../../../../Math/Algebra/Jets/Audit/AuditScalarJetIBP.lean) and
  [verification](../../../../topics/derivative-ibp/verification.md).

The scalar implementation uses Mathlib polynomial derivations and the
repository's proved quotient descent. The selected Physlib even derivations
remain available for a subsequent mixed-statistics construction; no external
SM or analytic package is imported into this scalar proof.
The surveyed Henning et al. papers guide the distinction between IBP and EOM
and between source and symbol presentations. Their counting, on-shell and
amplitude claims are not premises or certified comparisons; see the
[source register](../../../../topics/derivative-ibp/references.md).

The later [internal-linear and mixed extension](MIXED_JET_IBP.md) proves the
mixed-statistics source bridge and arbitrary internal linear covariance in
separate modules. The scalar/permutation package above retains its own scope.
The later [direction/EOM package](DIRECTIONAL_JET_EOM_IBP.md) and its
[Lorentz consumers](../Physics/LORENTZ_SCALAR_EOM_IBP.md) supply direction
covariance and free massless scalar EOM in separate modules. Gauge-covariant
commutators, Bianchi relations, momentum comparison and integrated-action
equality remain outside these packages.
The scalar result supplies no full EFT basis count or phenomenological result.
