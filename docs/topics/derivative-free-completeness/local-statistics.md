# Finite Local Statistics Compatibility

## Frozen Endpoint

From the existing finite local contractions and probes (normalization and
completeness both proved inputs), and genuine statistics representations on
local and flavor inputs commuting with their gauge/residual actions, derive
the statistics representation on the direct sum of flavor inputs. Its matrix
is computed from the contractions and probes, not defined by transport.
Prove the group law and residual commutation. This supplies the missing
input-action interface for the intrinsic isotypic classifier.

Residual group and flavor multiplicity remain arbitrary. No dimension,
compactness, numerical or literature premise is introduced. Forward pullback
on coefficients is still contravariant; the group law here is on inputs.
For arbitrary exchange relations, statistics stability of the relation space
remains a separately checked condition; it must not be assumed automatically.

## Result

[FiniteLocalStatistics](../../../Math/RepresentationTheory/FiniteLocalStatistics.lean)
proves the matrix identity, its multiplication law, and the actual statistics
representation on `I →₀ X`. Residual commutation is proved from the local/flavor
commutation certificates. Its matrices agree with the earlier exchange matrices.

[FiniteLocalIsotypicCompleteness](../../../Math/RepresentationTheory/FiniteLocalIsotypicCompleteness.lean)
proves compatibility with the coefficient pullback and composes the local
classification with nonredundant residual-Hom block coordinates. For a genuine
units-valued character, `characterQuotientEquiv` gives the statistical sector
as Hom from the independent input quotient, with explicit probe extraction and
local-contraction reconstruction. `characterIsotypicEquiv` then gives the product
of residual Homs of its actual isotypic blocks.

[CharacterRelationStability](../../../Math/RepresentationTheory/CharacterRelationStability.lean)
derives statistics stability of character relations from the group law:
`b(g)(rel(s,u)) = rel(g*s,u) - chi(s) • rel(g,u)`.
No additional stability premise is imposed on this character case. Arbitrary
exchange presentations still require that condition separately.

The local dictionary is supplied with normalization and completeness proofs;
this theorem does not discover contractions or choose bases inside flavor
multiplicity spaces. This closes the local-action compatibility milestone, not
the full Li p/y/m/j-basis program. No new dependencies or literature assumptions
were introduced.

## Verification

The [persistent audit](../../../Math/RepresentationTheory/Audit/AuditFiniteLocalStatistics.lean)
checks 16 declarations transitively, allowing only `propext`, `Classical.choice`
and `Quot.sound`. Focused build passed at stage 01. Full-build verification
is recorded in the [topic overview](README.md).
