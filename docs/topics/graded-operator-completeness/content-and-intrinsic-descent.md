# Content Orbits And Intrinsic Mixed Descent

## Verified Statements

[MixedContentOrbits](../../../Math/RepresentationTheory/MixedContentOrbits.lean)
indexes typed profiles by their actual fermion/boson permutation orbits. Its
`equiv` and `selectedEquiv` identify the full or selected mixed coefficient
space with a product of independently constructed typed ordered spaces. The
representative is internal; it is not a chosen contraction dictionary.

[MixedContentGrading](../../../Math/RepresentationTheory/MixedContentGrading.lean)
restricts these components by integral charges and positive engineering weights.
The selected supports are proved permutation-stable. Arithmetic support does
not replace gauge invariance.

[MixedCoinvariantCompleteness](../../../Math/RepresentationTheory/MixedCoinvariantCompleteness.lean)
constructs commuting exterior/symmetric actions from commuting actions on the
fields. For every natural pair of degrees its `equiv` takes actual combined-group
invariant functionals to residual Hom on local coinvariants, with inverse and
generator evaluation. `allEquiv` identifies the product of degree coefficient
spaces with the dual of a direct sum of residual carriers. All-degree zero and
existential nonzero criteria follow without a finite search cutoff.

[TypedMixedExchangeQuotient](../../../Math/RepresentationTheory/TypedMixedExchangeQuotient.lean)
constructs the span of signed identical-fermion exchanges and symmetric
identical-boson exchanges on heterogeneous ordered tensors. Its `vanish_iff`
proves equality with the actual typed exchange conditions, and `equiv` proves
two-sided Hom descent to the constructed quotient. The proof includes arbitrary
degrees and zero-degree cases; no flavor dimension is assumed.

[LocalRelationHom](../../../Math/RepresentationTheory/LocalRelationHom.lean)
imposes an independently supplied stable relation module after local
coinvariants by mapping its generators through the quotient. The constrained
coefficient equivalence has a constructed inverse and evaluation formula.

[TypedMixedSeparatedHom](../../../Math/RepresentationTheory/TypedMixedSeparatedHom.lean)
now connects the typed exchange input to an independently constructed residual
carrier `(L_c)_G ⊗ M_c` modulo the images of the actual signed exchange relations.
Local and residual stability and the local/flavor regrouping are proved. Its
`equiv` and `familyEquiv` are two-sided linear equivalences, with no local basis
or spanning certificate as a premise.

[GradedMixedCompleteness](../../../Math/RepresentationTheory/GradedMixedCompleteness.lean)
assembles the content factors into the full or permutation-stable selected
coefficient space, proving prohibition and existential nonzero iff. Its
all-degree dual is the product of coefficient spaces and the Hom of the
direct-sum residual carrier. Vanishing at every finite bound is equivalent to
all-degree vanishing; this supplies no uniform finite search cutoff.
[MixedContentBounds](../../../Math/RepresentationTheory/MixedContentBounds.lean)
proves that positive weights give finitely many contents under each bound,
including variation of both fermion and boson slot counts.

## Scope And Remaining Connection

These are checked algebraic components, not yet the completed A–D endpoint.
The separated field-content residual and graded product connections are now
constructed. Explicit SM six/seven-dimensional comparison maps and connected
regressions remain. The intrinsic all-degree coinvariant theorem alone is not
substituted for those acceptance conditions.

No AutoEFT, dependency change, numerical computation, finite-dimensional flavor
hypothesis, averaging, semisimplicity or external basis premise is introduced.

## Verification

Verification for this checkpoint is recorded in the topic overview after the
focused strict audit and full build. The persistent audit is
[AuditGradedOperatorFoundations](../../../Math/RepresentationTheory/Audit/AuditGradedOperatorFoundations.lean).
