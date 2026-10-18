# Remaining bridges after the consecutive colored attempts

The [results](colored-completion-results.md) prove actual Q and conjugate-Q
square/degree-ten branches, arbitrary unrestricted color tensor words,
several restricted positive pairings and compatible joint SU2 iff criteria.
They also classify actual `Q^2 conjugate-Q^2` all-Higgs support. The two
original general colored endpoints remain open.

## Higher exterior degrees

The still-needed Q statement is a complete equivariant split of
`Lambda^n(C^3 tensor C^2weak tensor C^2spin)` for the remaining middle degrees
4 through 6, with actual color summands, both SU2 labels, and verified
inverses/exhaustion. Complementary duality then covers degrees 7 through 9.
The needed output cannot be an opaque Hom or an assumed matching list.

The [subsequent cubic bridge](colored-middle-results.md) removes the
dimension-three restriction. Its [further resolution](colored-cubic-resolution-results.md)
now decomposes `Hook(color tensor weak)` into four actual branches and
completes all six Q/conjugate-Q cubic summands, including degree-nine duals.
The middle-degree obligation above is therefore reduced to degrees four
through six; it is not closed in its entirety.

The inspected general route is the sign-isotypic/skew Cauchy decomposition,
followed by restriction of the resulting factor on the four-dimensional
weak/spin tensor. This requires the actual Young-component embeddings and
complete projection relations, not just an equality of characters or a
list of plausible summands. The degree-two case is now constructed locally;
the original three-dimensional-color cube alone did not apply directly to
the six-dimensional color/weak space in a Q cube. The cubic obstacle is
now resolved by universal hook maps and finite-length cancellation, rather
than by assuming a general Schur branching theorem.

Pinned TauCeti is `b9e2e182804073eb92718b68a9baf37df8e189bd`.
`RepresentationTheory/ClassicalGroups/WeylModule/SchurWeyl.lean` provides
proved character and dimension identities, including
`char_weylRepOfShape_diagramOf_eq_sum_spechtChar` and
`sum_finrank_spechtModule_mul_char_weylRepOfShape_diagramOf`. These
inspected declarations do not themselves provide the required skew exterior
splitting under the retained product group. No such conclusion was inferred
from the module name. A further bounded Young-projector construction or a
semantic skew-Cauchy bridge remains a separate theorem-level obligation.
This is a report of the inspected route, not proof that another route is
impossible or that every general Schur foundation is necessary.

## General restricted color coupling

The new triality iff is for complete defining/dual tensor powers or ordered
binary words. Projecting these onto symmetric, trace-free or higher Young
components may remove a coefficient. The paired positive families construct
witnesses on their actual restricted summands; they do not justify replacing
the general rule by triality alone.

The same [continuation](colored-middle-results.md) now proves a closed
positive iff for arbitrary products of exterior-restricted defining/dual
color leaves, including all capacity exclusions. Symmetric, trace-free and
higher Young restrictions are outside that new iff.

The [trace-free continuation](colored-restricted-results.md) separately
closes arbitrary tensor words of the defining/dual trace-free endomorphism
branches: only a singleton is forbidden. Their actual dual-endomorphism
equivalence and all positive pair/triple gluing are proved. Arbitrary
mixtures with symmetric or higher Young color components are still open;
neither restricted word result supplies that general coupling rule.

The remaining semantic target is an iff between an actual SU3 tensor Hom
for reachable color labels and an explicitly bounded positive combinatorial
witness (for example a nonnegative Berenstein-Zelevinsky triangle/path with
its boundary and compatibility conditions). It needs actual representation
identification and both occurrence/exclusion directions. A bare integer
predicate, unknown intertwiner, assumed irreducibility or signed Laurent
coefficient is not a substitute for this bridge.

`.../WeylModule/SpecialLinear.lean` explicitly leaves irreducibility and
exhaustion of the restricted rational modules beyond its scope; its proved
restriction/shift/character results were inspected. The targeted local
searches did not yield a ready semantic positive-coupling theorem for this
SU3/SM setting. No pinned dependency was changed.

## Literature checked as guidance, not a premise

- Rasmussen and Walton, [su(N) tensor product multiplicities and virtual
  Berenstein-Zelevinsky triangles](https://arxiv.org/abs/math-ph/0010051v3),
  v3 (2001), J. Phys. A 34, 11095–11105. Its stated nonvanishing application
  uses inequalities on Dynkin labels. This motivates a positive witness
  interface; it has not been imported as an input or proved applicable to
  the concrete Lean modules.
- Berenstein and Zelevinsky, [Tensor product multiplicities, canonical bases
  and totally positive varieties](https://arxiv.org/abs/math/9912012v1),
  v1 (1999). The authors give polyhedral lattice-point descriptions for
  tensor products of simple finite-dimensional complex semisimple Lie
  algebra modules. Transferring such a theorem to the actual compact SU3
  actions and proving the concrete module identifications is an additional
  semantic task, not automatic library reuse.

These references remain research guidance. No assertion of paper-wide
verification, new literature premise or completed general classification
is made. Numerical rank/character-table fallback and an assumed desired
branching/coupling theorem were not used.
