# LLHH Graded Completeness

## Result

[GradedWeinbergComparison](../../../../../Physics/StandardModel/Operators/Weinberg/GradedWeinbergComparison.lean)
identifies the independently defined actual SM Weinberg sector with the
constructed residual quotient Hom at mixed degree `(2,2)`:

\[
\mathcal C_{LLHH}\simeq\mathrm{Hom}_R(Q_{2,2},\mathbb C)
\simeq\mathrm{Hom}_R(\mathrm{Sym}^2F,\mathbb C).
\]

`onSMEquiv` is the first equivalence; `comparison` is the second. Extraction
and reconstruction commute with `WeinbergSMInterface.homEquiv`. Both inverse
laws and total prohibition/nonzero iff are proved. `oneGenerationEquiv`
identifies the generic quotient Hom with `ℂ` for trivial one-generation flavor.

## Inputs And Conventions

The residual group and complex lepton multiplicity module are arbitrary;
no finite-dimensionality, compactness or self-duality is assumed. One Higgs
doublet has trivial residual action. The independent input is exterior-square
leptons tensor symmetric-square Higgs, not four alternating fields.
The existing surjective physical-group projection and proved hypercharge
cancellation supply `WeinbergSMInterface.reducedEquiv`. The generic local group
is weak times left Weyl, with singleton lepton and Higgs species alphabets.
The Higgs multiplicity carrier `ℂ` is removed by the tensor-unit equivalence.

## Proof Structure And Normalization

`leptonEquiv` and `higgsEquiv` prove singleton evaluation and tensor-unit removal
equivariant. Their exterior/symmetric powers define `domainEquiv`. Singleton
support is automatic, yielding `inputEquiv` into the generic supported family.
`inputEquiv_pure` preserves pure generator evaluations exactly, with no extra
factorial. Signed lepton and unsigned Higgs exchanges are handled by the general
mixed quotient, including its proved inverses.

Composing generic quotient completeness with the physical projection gives the
actual SM equivalence. The old symmetric-flavor classification is a comparison
target, not a premise of the coefficient-space decomposition theorem. Reducible private group instances
align the old/new interfaces without changing assumptions or normalization.
Mathlib `irreducible_def` preserves a proved definition equation for the large
physical equivalence while avoiding costly kernel reduction.

## Verification

The [persistent audit](../../../../../Physics/StandardModel/Operators/Weinberg/Audit/AuditGradedWeinbergComparison.lean)
checks the interface, pure formula, both comparisons/inverses, nonzero criteria,
one-generation control and definition equation transitively. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Commands and compatibility
verification are in the [topic results](../../../../topics/graded-sector-regressions/results.md).

## Boundaries And References

Two identical Higgs slots do not constitute a multi-doublet model. This is a
dimension-five fixed-content consumer, not a new all-content classification,
derivative/EOM/IBP result, arbitrary-group decision algorithm, or mass/rate
prediction. See [Physics assumptions](../../inputs/Physics/ASSUMPTIONS.md), the
[input dictionary](../../../../topics/graded-sector-regressions/interfaces.md) and the
[separate Weinberg literature certificate](LI_WEINBERG_BASIS.md).
This internal connection theorem does not extend literature coverage.
