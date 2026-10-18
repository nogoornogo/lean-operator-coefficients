# E6 finite-certificate feasibility boundary

This is a bounded source/interface review, not a completed replacement or a
new verification of the retained integer calculations.

## Existing route

[LieCertificateChecks](../../../Math/LieGroups/E6/Minuscule/LieCertificateChecks.lean)
connects sparse integer certificates to the pinned simple generators. Its
remaining substantive closed checks are:

- E6/D5 provenance: 78/45 basis vectors are generators or earlier brackets.
- Generator closure: 12×78 and 10×45 bracket expansions.
- Dual pairing: 78² and 45² pairings, plus nonzero scales.
- Actual-generator and selected-generator equalities.

[MatrixLieCertificate](../../../Math/LieAlgebras/MatrixLieCertificate.lean)
proves abstractly that these checks imply generation, independence and dimension.
It does not derive their integer hypotheses. Dividing these checks into cases
alone would retain the same unexplained certificate premises.

## Interfaces inspected

[D5Blocks](../../../Math/LieGroups/E6/Minuscule/D5Blocks.lean) gives invariant
16/10/1 coordinate blocks and simple-generator support by a grading. It does
not split the generated algebra into its individual root directions or derive
the bracket coefficients. The blocks alone therefore do not replace either
closure or the dual pairing.

The pinned dependency's `TauCeti.Algebra.Lie.E6.Minuscule.Basic` supplies
minuscule weights, simple generators and their Serre system. Its `RootDatum`
interface identifies simple-root torus characters, rather than furnishing the
required full matrix root basis. Those are useful inputs, not the missing
matrix-basis reconstruction theorem.

The local [MatrixLieBasis](../../../Math/LieGroups/E6/Minuscule/MatrixLieBasis.lean)
and [GeckComparison](../../../Math/LieGroups/E6/Minuscule/GeckComparison.lean)
are downstream of the very independence/dimension certificate under review.
Reusing their Cartan independence or faithful comparison as an independent
replacement would be circular. In particular `generatedGeckEquiv` uses
`generated_finrank`, which uses the current matrix-Lie dimension theorem.

## Stopping condition reached

A structural replacement needs an independently connected full root-direction
matrix family, proofs of generator action/bracket closure on that family,
Cartan extraction and independence, and a bridge back to the existing pinned
matrices. No such complete upstream interface was identified in the inspected
route. Building and connecting it is a separate Lie-representation foundation,
which the frozen plan excludes. No E6 source, check, limit or audit has been
changed, and no numerical table has been hidden behind a generated definition.
The retained obligations above remain explicit. This is a scoped feasibility
stop, not a theorem that structural replacement is impossible.
