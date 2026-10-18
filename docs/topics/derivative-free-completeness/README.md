# Derivative-Free Operator Completeness

- ID: derivative-free-completeness
- Status: completed
- Result type: algebraic completeness
- Working branch: `proof/derivative-free-completeness`
- Integration target: `master`
- Parent exception: work began on the unmerged `refactor/selection-rules-paths`
  lineage. On stage 01 the user explicitly authorized integration of the
  completed lineage into `master`.

## Endpoint And Scope

Prove independent input-relation quotients and inverse residual-Hom completeness,
then extend statistics to arbitrary tensor degrees, intrinsic nonredundant
isotypic coordinates and finite local contraction actions. Residual groups and
flavor dimensions remain arbitrary. Local dictionaries carry proved normalization
and completeness certificates; they are not discovered by the framework.
No uniform exterior realization or full SMEFT enumeration is claimed.
Successive frozen statements and historical checks are retained in
[checkpoints](checkpoints.md).

## Proved Results

- Stable-relation quotients, inverse Hom descent, finite local exchange
  coordinates and a physical Weinberg consumer. See the
  [proof dossier](../../proof/current/core/Math/RELATION_COMPLETENESS.md).
- [Two-slot Young components](two-slot-young.md), their independent symmetric
  and exterior square carriers, inverse laws and normalized generator formulas.
- [Finite statistics averaging](../../../Math/RepresentationTheory/FiniteStatisticsQuotient.lean):
  quotient/invariant equivalence and character twists over fields with
  invertible finite-group cardinal.
- [Arbitrary-slot statistics and Young projectors](arbitrary-slot-young.md):
  residual-compatible tensor permutations and individual mixed projectors.
- [Intrinsic isotypic coordinates](isotypic-residual.md): actual nonredundant
  direct sums and residual-Hom products; complex tensor statistics have injective
  Specht labels and supported-partition coordinates without finite flavor.
- [Finite local statistics connection](local-statistics.md): computed exchange
  matrices define a genuine input representation; coefficient pullback is
  compatible. Character relations have proved statistics stability, an actual
  quotient-Hom equivalence with extraction/reconstruction, and a final
  isotypic block-Hom product equivalence.

The local-action compatibility milestone and
[roadmap 1](multiplicity-coordinates.md) are complete. Actual blocks now have
chosen simple-copy multiplicity coordinates with full residual actions,
inverse Hom classification, change-of-choice equivalences and a concrete
non-diagonal local dictionary conversion. Multiplicity indices remain arbitrary.

## Remaining Roadmap

Roadmap 1 has passed its frozen endpoint and this topic is closed. Roadmaps 2
and 3 are deferred to possible future topics; there are no remaining obligations
under this topic's acceptance gate.

1. Completed: explicit simple-copy multiplicity coordinates and proved finite
   local dictionary conversions, with residual-Hom and character-sector consumers.
2. Deferred: identify those choices with specified Li p/y/m conventions. No direct sum
   of all tableau images or complete Li construction is currently claimed.
3. Deferred: treat j-basis only with a specified channel and Casimir interface.
   Derivatives, EOM/IBP and amplitudes remain a separate foundational project,
   not prerequisites silently added to this stage.

Li et al. motivates this roadmap, not an assumed Lean theorem; see the
[literature comparison](../operator-completeness-interface/README.md#relationship-to-li-et-al).
No matching, rates, RGE or numerical dynamics is added. Stop if a frozen
statement has a counterexample or needs essential new premises beyond the
specified actions, relations and proved local completeness.

## Verification

On stage 01, the intrinsic isotypic milestone (`checkpoint 01`) passed 23 strict
transitive checks, full `lake build` (6,364 jobs), layout (1,040 modules), links
(381 documents, 2,604 links), and `git diff --check`.

The local statistics milestone passed its focused audit (16 strict transitive
checks), full `lake build` (6,368 jobs, no warnings/errors), layout (1,044
modules), links (383 documents, 2,623 links, no errors), and `git diff --check`.
Audits allow only standard Lean axioms. Pins and allowlists are unchanged;
no merge is authorized.

Roadmap-1 first milestone: 14 additional strict transitive checks passed;
full `lake build` passed (6,371 jobs, no warnings/errors), layout passed
(1,047 modules), links passed (384 documents, 2,630 links), and
`git diff --check` passed. See [its scope](multiplicity-coordinates.md).

Roadmap-1 completion: `lake build Math.RepresentationTheory.Audit.AuditMultiplicityCoordinates`
passed 31 strict transitive checks; full `lake build` passed (6,373 jobs,
no warnings/errors); layout passed (1,049 modules); links passed (384 documents,
2,636 links); `git diff --check` and 14 docs/layout regression tests passed.
No new assumptions, pins or audit
allowances were introduced. Master integration was explicitly authorized on
stage 01; Git ancestry records the resulting merge.
