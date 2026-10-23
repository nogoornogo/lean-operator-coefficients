# Heeck–Le Existing-Sector Certificates

## Result

The normalized contractions in Heeck–Le's dimension-six DUQL, QQUE, QQQL
and DUUE entries realize the independently classified exterior coefficient
spaces. The two specified dimension-nine right-handed u²d⁴ contractions,
with species-preserving exchanges, span the full 25-dimensional invariant
local space. A selected 25-element exchange orbit is a basis. Transport to
typed residual Hom retains all four statistics constraints and has two-sided
inverse maps to the physical sector.

This is an existing-sector comparison, not verification of the whole paper
or its operator counts through dimension eleven.

## Inputs And Citation Role

[Heeck–Le, arXiv:2604.25134v2](https://arxiv.org/abs/2604.25134v2)
supplies candidate data, not a completeness premise. The relevant unnumbered
tables are Section 6, printed page 21, and Section 9.4, printed page 23.
The [source dictionary](../../../../topics/heeck-le-sector-comparison/source-recovery.md)
pins checksums and slot orders. Section 2.1 explicitly uses three generations.
The formal algebraic extensions below are our conclusions, not an attribution
of an arbitrary-flavor theorem to the source.

Brackets are interpreted as the existing algebraic Weyl epsilon pairings.
Right-handed physical species use the existing right Weyl representations.
No four-component Dirac C-matrix equivalence, spacetime-field semantics,
amplitude normalization, or LSZ theorem is inferred. Actual carriers require
the existing equivariant identification interfaces. Residual symmetry H is
an arbitrary group with specified complex representations.

## Four-Fermion Proof Structure

Each family has a separate certificate:

- [DUQL](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/HeeckLeDuqlCertificate.lean):
  `ordered_apply` matches D,U,Q,L literally. Distinct-species descent is the
  complete inverse. Finite bases require bases of the four flavor carriers;
  unrestricted counts additionally require trivial induced residual action.
- [QQUE](../../../../../Physics/StandardModel/Operators/BaryonOne/Qque/HeeckLeQqueCertificate.lean):
  `literal` matches physical Q,Q,U,E order. `restriction_candidate` proves
  that the normalized exterior inverse restricts to this contraction; both
  inverse identities hold on the symmetric-Q residual subspace. The factor
  1/2 is the independently established repeated-species lift normalization.
- [QQQL convention](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/HeeckLeQqqlConvention.lean)
  and [certificate](../../../../../Physics/StandardModel/Operators/BaryonOne/Qqql/HeeckLeQqqlCertificate.lean):
  weak (03)(12), spin (01)(23) gives local seed `!![-1,0;1,0]`.
  Its symmetry components are `(-1/6,-1/2,-2/3,1/3)`. The explicit six-term
  orbit inverse and source `-f₀-f₁/3+f₃` prove actual raw alternating descent
  equals the complete constrained inverse. Raw flavor permutations are not
  an independent basis; the domain already retains their relations.
- [DUUE](../../../../../Physics/StandardModel/Operators/BaryonOne/OtherFamilies/HeeckLeDuueCertificate.lean):
  D,U,U,E to U,U,D,E is even; the first bilinear reversal supplies a minus.
  The single cross-pairing source is `swap k`, so ordered coordinates are
  `(0,-swap k)`. Actual exterior alternation reconstructs
  `(k,-k-swap k)`, and is the complete inverse. The remaining Hom is
  unrestricted in the two U arguments, not assumed symmetric.

These residual four-family results require neither finite dimensionality
nor compactness or continuity. Finite coordinate/basis wrappers retain their
explicit additional conditions.

## Six-Quark Proof Structure

[Literal conventions](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkConvention.lean)
prove the color identities for triples (134)(025) and (124)(035), with spin
(01)(23)(45), in repository U,D,U,D,D,D order. The reorder has no net sign.
The seed arrays have only spin column 0: color columns `(-1,0,0,-1,1)`
and `(-1,0,-1,0,1)`.

[The rational presentation](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkData.lean)
is derived from these two separated sources and their original exchange words.
There is no supplied projected-seed, forward-matrix or inverse-matrix table.
[Symbolic extraction](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkExtraction.lean)
uses the invariant color/spin blocks, a ten-coordinate quotient with two kernel
parameters, five up-exchange pairs and five scalar coupling equations solved
by back substitution. A spin-block rescaling gives integer internal coordinates;
it does not rescale the physical contractions.

[The matrix presentation](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkMatrix.lean)
derives both inverse identities from uniform reconstruction over an exact field
of characteristic zero. Existing rational certificate names are compatibility
wrappers for that derivation, not stored inverse entries or closed numerical
matrix products. [Coordinate certificates](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkCertificate.lean)
retain agreement with the actual exchange words.
[Local basis](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkLocalBasis.lean)
proves literal reconstruction and linear independence in the independently
defined invariant submodule, rather than merely checking a rank table.

[Residual transport](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/HeeckLeSixQuarkResidual.lean)
gives `statisticsEquiv`, `physicalEquiv`, actual-field `onFieldsEquiv`, and
literal local assembly. The 25 entries are constrained flavor maps, not free
Wilson coefficients. The typed Hom transport, coefficient and physical-sector
bridges allow arbitrary complex U,D after the
[basis-free inverse extension](GRADED_SIX_QUARK_COMPARISON.md).
No upper bound of three on either flavor dimension is needed for this result.
The scalar one-generation sector has finrank two and agrees with the existing
two-probe inverse. This is not a new flavor dimension formula for arbitrary H
or a certificate of the paper's complete dimension-nine term count.

## Verification And Limits

[The structural audit](../../../../../Physics/StandardModel/Operators/BaryonTwo/HeeckLe/Audit/AuditHeeckLeSixQuarkStructural.lean)
checks all declarations owned by the new source/block modules, including private
helpers, and excludes the old data/basis modules as imports. The
[readability topic](../../../../topics/proof-readability-review/README.md)
owns the replacement work and its verification.

The [strict audit](../../../../../Physics/StandardModel/Operators/Selection/Audit/AuditHeeckLeBasis.lean)
checks transitive axioms of all declarations in the comparison namespaces,
allowing only `propext`, `Classical.choice`, `Quot.sound`, and rejects imports
from the model layer. Literature completeness is not an axiom.
Commands and outcomes belong to the
[topic results](../../../../topics/heeck-le-sector-comparison/results.md).

Excluded: other dimension-nine chiralities, Higgs insertions, derivatives,
EOM/IBP, on-shell amplitudes, AutoEFT output, UV matching, rates, and a
whole-paper minimality/counting claim. The separate Li missing-component
certificate is neither a premise nor an error allegation against Heeck–Le.
