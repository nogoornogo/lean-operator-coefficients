# Exact certificates and multiplicity compression

After checkpoint `checkpoint 01`, the user resumed numerical classification.
The [numerical continuation](constant-results.md) now evaluates a specified
constant-content subset. The original generic bridge below remains conditional.

## Exact matrix computation

[ExactRankCertificate](../../../Math/LinearAlgebra/ExactRankCertificate.lean)
defines a certificate over a field for a rectangular matrix A:

    A = B*C,  L*B = 1,  C*R = 1.

The inner index type T gives `rank A = card T`. Multiplication rank
inequalities prove the upper and lower bounds; this is valid also for rank
zero and empty dimensions. Mapping the certificate along any field
homomorphism preserves the identities and proves the mapped rank and nullity.
In particular, rational witnesses certify the rank of their complex images.

[The generator](../../../tools/exact-rank/README.md) performs rational Gaussian
elimination using Python `Fraction`, and emits Lean source containing the
factorization, left/right inverses and a complex-rank theorem. The three
matrix identities use `decide +kernel`. Python results are never accepted as
premises. The committed generated examples cover fractions and a rectangular
rank-two matrix, a full-rank matrix requiring a pivot row swap, a zero matrix,
and matrices with zero rows or zero columns.

This is an exact certificate-producing calculation for rational input, not
an executable decision procedure for arbitrary abstract complex numbers. The
generator's universal correctness/termination is not formalized; every emitted
certificate must be built and audited. Incorrect output cannot prove a rank
through this interface. No floating-point tolerance or unchecked native axiom
is used. The generic theorem is available for other exact fields as well,
but no algebraic-number field backend has been added.

## All-content order redundancy removed

[PatternMultiplicityEquiv](../../../Math/RepresentationTheory/PatternMultiplicityEquiv.lean)
proves equality of the actual exterior source submodules for any two words
of the same length with identical species counts. Reordering exterior
generators changes signs, but not their span. The constructed representation
equivalence is the identity on their common ambient exterior elements.
The theorem retains arbitrary supplied species representations.

[SMRankMultiplicity](../../../Physics/StandardModel/Operators/SMRankMultiplicity.lean)
transports this through the Higgs tensor factor and actual local kernel. For
every flavor input, degree, pair of equal-count words, m and delta, it proves
`rank(constraints p m delta) = rank(constraints q m delta)`. Thus rank depends
only on content multiplicities, not the order of the species word. This is
an unconditional compression theorem, not an evaluation of the remaining
count-indexed ranks. It does not reduce distinct occupation vectors to one.

## Explicit conditional connection

[SMExactRankBridge.rank_from_certificate](../../../Physics/StandardModel/Operators/SMExactRankBridge.lean)
accepts a *proved* linear equivalence from the actual local invariant
coefficient space to the complex kernel of a rational matrix A. Given a rank
certificate with inner size r and A having c columns, it returns

    actual rank = actual carrier dimension - (c-r).

It permits a compressed coordinate matrix of a different size. The semantic
equivalence is an explicit theorem parameter, not a new assumption on all SM
contents. The audit of this implication does not construct its parameter.

## Attempt boundary and next prerequisite

Two routes were inspected within the recorded plan:

1. Exact matrix certificates now work, but the original generic matrices use
   a classical statistical basis and `Circle.exp 1` samples. Equal-count
   transport removes word redundancy without providing a rational model of
   their constraints. A uniform construction of an exact coordinate matrix
   and a proof of its kernel equivalence is still needed. Rationality of the
   original entries is neither assumed nor asserted.
2. Character/multiplicity compression can avoid materializing these matrices.
   `SMColorIntegralBasis` gives integral weight spanning, not the invariant
   multiplicities of all statistical images. `ExactSMWeightMultiplicity`
   treats the supplied SM spectrum, not arbitrary exterior content.
   `CompactHomDimension` gives a Haar-integral formula under compactness and
   continuity, not an executable extraction formula for the actual paired
   Weyl/gauge action. Applying a compact replacement to that action requires
   its own verified connection.

The remaining theorem-level prerequisite is therefore a **uniform exact
coordinate/kernel construction, or an invariant-multiplicity extraction
theorem, for the actual content source**. LLHH supplies that connection for
one content via its existing contraction classification. No comparable
all-content construction was obtained in this attempt. Under the recorded
foundation gate, the current result stops here rather than treating the
conditional bridge as a completed classification. No full-table brute-force
enumeration was attempted. All-content numerical ranks and the corresponding
all-degree 572-assignment classification remain open.

The [literature record](../llhh-kernel-rank/literature.md) remains guidance;
no cited theorem is inserted as an axiom. This milestone validates neither
BasisGen nor a paper-wide operator list.


The prerequisite above described the initial certificate/compression checkpoint.
The subsequent [L/conjugate-L weight result](lepton-multiplicity-results.md)
and [Q/conjugate-Q exact-coordinate result](q-gaussian-results.md) now supply
actual uniform local nullity/support formulas for these constant-species
families. They do not provide an all-mixed-content classification or enumerate
the 572 assignments. The original partial CSV remains unchanged.
