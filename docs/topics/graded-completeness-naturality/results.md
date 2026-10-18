# Results

The frozen A-D endpoint is complete. This is degree-uniform integration of
existing algebraic completeness, not a new physical-sector classification.
The [completed-result dossier](../../proof/current/core/Math/GRADED_COMPLETENESS_NATURALITY.md)
owns the theorem description and boundaries.

## A. Independent Maps

Stable-relation maps descend directly to local coinvariants and the image of
exchange relations. Quotient generator formulas, equivalences and inverses are
proved in `RelationQuotientNaturality`, `LocalCoinvariantNaturality` and
`LocalRelationNaturality`. The actual typed mixed exchange relations are
preserved by species-wise tensor maps.

`TypedMixedCarrierNaturality` constructs the ordered/separated carrier
identification without using coefficient completeness.
`TypedMixedLocalTransport` and `TypedMixedSeparatedTransport` use that
identification and directly induced quotient maps. Neither defines output
transport by conjugating an input map with the operator completeness equivalence.
`LocalMultiplicityEquiv` supplies the paired-field interface from factorwise
local/multiplicity equivalences.

Direct quotient maps and species/typed input pullbacks obey identity/composition
laws. Ordered residual Hom composition and separated Hom identity are proved.
`CompletenessSquareLaws` carries these input laws to independently constructed
output maps via the already proved squares, without defining those maps.

## B. Degree-Uniform Squares

`GradedCompletenessFieldTransport` proves that actual exterior/symmetric field
pullback agrees with the ordered maps and the independent content-wise residual
Hom maps. Extraction and reconstruction commute at every `(n,m)`, including
zero degrees, with stable support selection and with all-degree products and
direct-sum functionals.

`GradedCompletenessRestriction` and `GradedCompletenessAllRestriction` prove the
same diagrams for residual-group restriction along any `j : H' -> H`.
All-degree Hom maps use independent factor maps and the direct-sum universal
property. Bounded engineering/charge support is an instance with the same
support predicate and weights; there is no new cutoff assumption.

## C. Restriction And Symmetry

Restriction is injective on actual coefficients and on quotient Hom factors,
selected products and all-degree functionals. Consequently allowance passes
from larger symmetry to smaller symmetry; prohibition passes from smaller to
larger symmetry. The converses are not asserted. Surjective `j` gives
two-sided equivalences compatible with completeness, for the already supplied
target actions pulled back along `j`. Descent of an arbitrary action is not
inferred from surjectivity.

The preserved-data application uses the proved containment obtained by adding
data to a stabilizer, not a new classification of that stabilizer.

## D. Regressions And Final Verification

Exact Lean controls cover a nontrivial mixed `(1,2)` field transport, a
surjective cover, a subgroup restriction that is not surjective, and
preserved-data stabilizer containment. The persistent audit permits only
`propext`, `Classical.choice` and `Quot.sound`.

Final checks on the topic branch:

- `lake build Math.RepresentationTheory.Audit.AuditCompletenessNaturality`:
  3,367 jobs; 110 strict transitive checks passed, with no focused-build warnings.
- `lake build`: 6,547 jobs passed, including the existing graded foundation,
  BNV, six-quark and Weinberg comparison audits and all three aggregates.
- `node tools/layout/check-layout.mjs`: 1,220 modules; no layer, import,
  cycle, aggregate or relocation violations.
- `node tools/docs/check-links.mjs`: zero link/fragment errors.
- `git diff --check`: passed.

Verified checkpoints are `checkpoint 01`, `checkpoint 02`, `checkpoint 03`, `checkpoint 04` and
`checkpoint 05`; the completion-record commit follows them in Git. The first four
checkpoint audits were not full-build baselines. The final full build above
is the acceptance evidence for this topic.

## Remaining Boundaries And Integration

No acceptance task remains. Dependencies, physical scope, the root README and
literature coverage ledgers are unchanged. Arbitrary Hom computation, species
relabeling, local-group changes, derivatives, EOM/IBP and new sectors remain
outside scope.

## Master Integration

By explicit user direction, the topic was merged into `master` with
`git merge --no-ff` at `checkpoint 06`. On the merged tree, the focused audit again
passed all 110 strict transitive checks (3,367 jobs), and `lake build` passed
6,547 jobs. Layout, local Markdown links and `git diff --check` also passed.
The historical working-branch name above is retained; the local topic branch
is retired after reachability and worktree safety checks. No remote push was
performed.
