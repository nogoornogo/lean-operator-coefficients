# Finite Certificates And Their Limits

## Checked Inputs

[FiniteDerivativeCertificate](../../../Math/RepresentationTheory/FiniteDerivativeCertificate.lean)
turns a basis of an actual finite source and a proved spanning family of its
relations into inverse coefficient/coordinate maps. Coordinate conditions
annihilate the relation rows and impose the full specified group on each
basis vector. Reconstruction, forbidden and allowed equivalences follow.
This is a certificate consumer, not an algorithm inferring relation spans or
replacing the group with infinitesimal generators.

[FiniteDerivativeScalarControl](../../../Math/RepresentationTheory/FiniteDerivativeScalarControl.lean)
supplies those obligations for the complete one-direction quadratic scalar
source: two actual monomials, the off-shell relation row (1,1), and the full
on-shell relation span. This independently checks the certificate's source
and relation connection; it does not certify C1's two-species table.

[ScalarZeroDerivative](../../../Math/Algebra/ScalarZeroDerivative.lean)
reconstructs the entire one-species zero-derivative grade from its unique
monomial at every field degree n. The
[physical certificate](../../../Physics/FieldTheory/Jets/ScalarZeroDerivativeCertificate.lean)
proves that this grade's actual image in the full free Lorentz EOM/IBP
quotient is one-dimensional. Its inverse coordinate map is restriction of
a globally invariant coefficient, not an assumed extension of a selected
functional. In particular, the C2 four-field degree-zero image has dimension 1.

[JetConstantProjection](../../../Math/RepresentationTheory/JetConstantProjection.lean)
kills all positive-order jets and all total derivatives, and commutes with
arbitrary linear direction changes. Its
[scalar consumer](../../../Physics/FieldTheory/Jets/ScalarConstantCoefficients.lean)
annihilates the entire free differential EOM ideal and full divergence range.
For every n it gives an actual Lorentz-invariant coefficient taking phi^n to 1.
The interacting cubic target has the exact condition

\[
(\exists f,\ f(\phi^3)=c)\quad\Longleftrightarrow\quad\lambda c=0.
\]

Thus a nonzero cubic value is possible exactly when lambda=0. This sharpens
the earlier necessary coupling condition for that target, without classifying
every coefficient or asserting an interacting homogeneous decomposition.

## C2 Positive Derivative Degrees — Partial Stop

The structural route combines the existing metric contraction and free
first-variation relation with the new actual global separating coefficients.
It proves the complete degree-zero image and retains the actual vanishing
of the specified two-derivative representative. Constant-jet coefficients
vanish on every positive derivative degree, so they cannot separate the
four-derivative candidate or prove a complete invariant span there.

The coordinate route reruns the exact
[finite diagnostic](../../../tools/derivative-literature/check-scalar-lorentz.py)
and tests the new certificate on a completely reconstructed actual source.
The diagnostic still has source sizes 1/20/305, EOM/IBP ranks 0/11/235 and
infinitesimal constrained dimensions (1,0,1). No matrix from that script is
imported into Lean. Applying the certificate to its positive-degree rows
still requires a proved coordinate identification, equality with the full
selected relation preimage, and sufficiency of the Lie constraints for the
specified full Lorentz action. These are not proved by finite dimensionality
or by the certificate's existence. No full (1,0,1) coefficient count is claimed.

## C4 — Independent Partial Stop

The original stop below is retained as checkpoint evidence. The separate
[Higgs successor](../higgs-quartic-four-completeness/results.md) now closes
the native free/gaugeless whole-grade invariant-coefficient target, with
its own proof and [verification](../higgs-quartic-four-completeness/verification.md).
This does not change the scope of the earlier checkpoint.

The structural route uses A's actual doublet/dual dictionary and canonical
paired-jet contractions. It removes the earlier ambiguity about formal
component labels, but supplies neither all four-direction contraction
identities nor complete invariant reconstruction for H4D4. Invariance of
the three particular contractions in the combined action, quotient
separation and invariant completeness remain separate obligations.

The coordinate route compares the existing three raw probes with the new
certificate's relation-annihilation obligation. The Lean theorem
`probe_not_ibp` evaluates a genuine total derivative to 1. Such a probe
cannot be a row-coordinate decoder for the actual EOM/IBP input. Replacing
it requires new globally invariant annihilators and a complete relation
presentation; raw independence is insufficient. No three-coordinate
quotient equivalence has been constructed. The physical paired dictionary
is now available from A, but does not discharge these distinct obligations.

These are semantic/completeness stops after the two routes, not paper
contradictions or numerical-resource claims. C follows independently.
