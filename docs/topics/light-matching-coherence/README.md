# Light-Matter Matching Coherence

- ID: light-matching-coherence
- Status: completed
- Checkpoint detail: completed (actual-radical and joint full-species endpoints verified).
- Result type: conditional actual-radical exchange and joint full-species matching.
- Working branch: `proof/light-matching-coherence`.
- Integration target: `master`.
- Second-phase base: `checkpoint 01`.
- [Second-phase frozen statement and verification](joint-species.md).

## Frozen Endpoint

Use the existing Georgi-Glashow zero-mass n(10 + bar5) source, not a new
light-spectrum assumption. Lift the actual heavy-generator action to its
radical and evaluate against its dual. Recover the existing SU(5) currents
and exchange on retained fields. Derive compatibility with ordinary residual
centralizer actions from their existing multiplicity formula.

Routes: zero-radical equivalence and explicit generation-wise action;
species-preserving transport of the already generated coefficient. Audit
the remaining obligations before claiming a joint SM x H exterior endpoint.
Do not replace them by a coefficient nonzero/invariant premise.

The finite first milestone is actual radical current recovery and residual
compatibility. A reusable abstraction is justified only by the concrete
construction. Stop and record any additional theorem-level prerequisite
needed for full species identification. No vacuum, Yukawa, arbitrary mass,
amplitude or width construction; no dependency or axiom changes.

## Interfaces

- [Source](../../../GUT/SU5/SelectionRules/GeorgiGlashowSource.lean)
- [Centralizer](../../../GUT/SU5/SelectionRules/MatterSource.lean)
- [Currents](../../../GUT/SU5/Matching/HeavyCurrents.lean)
- [Exchange](../../../GUT/SU5/Matching/MediatorMatching.lean)
- [Previous matching](../sun-conjugate-matching/README.md)

## First-Milestone Verification

- `lake build GUT.SU5.Matching.LightRadicalExchange`: passed.
- `lake build GUT.SU5.Audit.AuditLightRadicalExchange
  Physics.StandardModel.Operators.Audit.AuditMediatorQqueEvaluation`: passed,
  22 + 2 strict transitive axiom checks, allowing only `propext`,
  `Classical.choice`, `Quot.sound`.
- Full `lake build`: passed, 5826 jobs. Existing warnings replayed; no new
  source warnings. No heartbeat, dependency pin or audit policy changes.
- Exact regressions: `python3 tools/qque/audit_one_generation.py` (4),
  `python3 tools/qque/audit_pairwise.py` (3),
  `python3 tools/qque/audit_contraction_uniqueness.py` (3): passed.
- `node tools/layout/check-layout.mjs`: passed, 775 modules.
- `node tools/docs/check-links.mjs`: passed, 294 Markdown files,
  1765 local links, 33 fragments.
- `git diff --check`: passed. Lean LSP unavailable; used focused builds.
- Commit this verified milestone and merge with no-ff to master; repeat the
  full build and consistency checks on the merged state. Git ancestry records
  integration; retain the topic branch, no push.

## First-Milestone Results

[LightRadical](../../../GUT/SU5/Matching/LightRadical.lean) uses exactly
`GeorgiGlashowSource.mass R` and its existing radical equivalence. There is no
new light-space or coefficient-nonzero premise. The retained ten operator is
applied identically in all generations, with zero on the bar-five component.
This is the retained ten contribution, not a reconstruction of every current
on the full 10 + bar5 UV matter. Its restriction to Q/up/e is derived from the
same exterior infinitesimal action as the original matching.

The existing centralizer multiplicity formula proves that this operator
commutes with every `R : OrdinaryAction H n`. Dual evaluation then proves
invariance of each current on the actual radical and its dual. No topology,
compactness or continuity of H is needed for this algebraic assertion. The
unitary-centralizer condition on R is retained, not silently weakened.

The Q map into the radical and up/e maps into its dual are injective.
Evaluation of the recomputed currents on these fields recovers the previous
six-channel currents exactly, for each supplied generation `a : Fin n`.

[LightRadicalExchange](../../../GUT/SU5/Matching/LightRadicalExchange.lean)
uses the same massive mediator operator and normalization as SU(5) matching.
It proves residual invariance of the exchange and its nonzero alternating
descent. `coefficient_on_fields` and `exterior_on_fields` identify its actual
values with the original ordered and exterior coefficients, respectively.
Nonzero descent requires a supplied `a : Fin n`, hence n > 0. It follows from
the original probe, not merely from nonzero ordered currents. Controls cover
one and three generations with arbitrary R.

The first milestone's ambient exterior carrier is the direct sum of three labelled
carriers K, K.dual, K.dual, with their respective spinors. Its invariance is
H x Lorentz. That carrier alone is not the independently classified full-SM qque sector
on the actual Q/up/e subrepresentations. In particular, a selected generation
is not asserted to be H-stable when R mixes generations. Recovered SM
invariance on retained coordinates and ambient H invariance must not be
described as a simultaneous SM x H identification without the next construction.

## Joint Species Connection

The [second milestone](joint-species.md) exhausts the canonical full Q/up/e
images by all-generation embeddings in this same radical and dual. Restricting
the actual currents gives simultaneous SM x H invariance and a nonzero
generated element of `FullLightSpeciesQque.Sector`. The existing completeness
equivalence gives its nonzero residual Hom and reconstructs this same element.
No independently nonzero coefficient, assumed H-invariance, or H-stable
single-generation selection is introduced.

The bounded joint-species endpoint is separate from general nonzero fermion masses,
SUN light-spectrum selection, Yukawa invariance, vacuum selection and physical
decay amplitudes, which remain outside this topic. The small reusable
[evaluation API](../../../Physics/StandardModel/Operators/MediatorQqueEvaluation.lean)
avoids expanding model-dependent carriers in exterior proofs. The new generic
finite-generation extensionality lemma is independent of the SU(5) application.
