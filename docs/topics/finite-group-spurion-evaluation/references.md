# Literature And Repository Source Register

Sources guide the proof; no external theorem premise is admitted.

## R1 — Spurion Saturation Context

B. Grinstein, X. Lu, C. Miró, P. Quílez, *Most general EFTs from spurion
analysis: Hilbert series and Minimal Lepton Flavor Violation*.

- Pinned source: [arXiv:2412.16285v1](https://arxiv.org/abs/2412.16285v1).
- Intended location: Sec. 2.2, Eqs. (2.4), (2.6), (2.8), as recorded in the
  [predecessor register](../all-degree-symmetry-protection/references.md#r2--spurion-saturation-and-mlfv).
- Role: motivation for comparing spurion evaluation with stabilizer invariants.
- Inspection: primary metadata and abstract checked for this planning pass;
  the predecessor records its own full-text inspection. Equation-level
  comparison is not reverified here.
- Limits: the abstract discusses generic vacuum values and arbitrary spurion
  powers. The proposed finite-group theorem at every value is to be proved
  directly; it is not a certificate of the paper's MLFV scenarios.

## R2 — Covariant Module Background

M. Brion, *Sur les modules de covariants*, Annales scientifiques de l'École
Normale Supérieure, série 4, 26 (1993), no. 1, pp. 1–21.

- Primary record: [DOI 10.24033/asens.1665](https://numdam.org/articles/10.24033/asens.1665/).
- Location: Sec. 1.2 corollary, printed p. 4, recorded in the
  [predecessor feasibility decision](../all-degree-symmetry-protection/feasibility.md).
- Role: background explaining the separate general algebraic-group boundary;
  not needed as a premise of finite interpolation and averaging.
- Inspection: bibliographic metadata checked here; geometric hypotheses and
  original-text inspection belong to the linked predecessor record.
- Limits: a covariant-module rank statement is not automatically pointwise
  evaluation surjectivity. No algebraic-group theorem is imported.

## Repository Inputs And Attribution

- [Polynomial evaluation](../../../Math/RepresentationTheory/PolynomialCovariantEvaluation.lean):
  source inspected; evaluation lands in actual stabilizer invariants.
- [Convention dictionary](../all-degree-symmetry-protection/interfaces.md):
  coordinate and dual conventions, not a general saturation proof.
- [Graded completeness dossier](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md):
  existing coefficient/Hom interface; exact consumer declarations must be
  inspected during implementation.

The finite-orbit separation/product and finite averaging argument in the
plan is a proposed direct construction. No specific literature attribution
or novelty claim is asserted for it. Record any additional source actually
used, including its exact theorem and conditions, before claiming a comparison.

## Integration Obligation

Before merge, reconcile R1/R2 and any subsequently used sources into
[the maintained literature list](../../proof/RELATED_LITERATURE.md). Add or
update entries with final result links, citation roles and inspection limits;
do not duplicate entries or present this plan as a proved literature bridge.

## Implemented Source Connection

The [proved result](results.md) uses direct finite interpolation and averaging.
Its [core dossier](../../proof/current/core/Math/FINITE_GROUP_SPURION_EVALUATION.md)
links the proof and coefficient consumer. No R1/R2 theorem is used as a premise.
The source register has been reconciled into RELATED_LITERATURE.md for this
result; recheck the final entries before a separately authorized merge.

The degree extension uses the pinned Mathlib modules
`Algebra.MvPolynomial.Degrees`, `CommRing` and `Monad`: total-degree estimates
for sums/products/powers and the monomial substitution formula. The project
proves the linear-substitution estimate and finite interpolation bound in
[FiniteGroupSpurionDegree](../../../Math/RepresentationTheory/FiniteGroupSpurionDegree.lean).
No new literature input or saturation premise is used; the maintained
literature list distinguishes the derived cutoff from the motivating sources.
