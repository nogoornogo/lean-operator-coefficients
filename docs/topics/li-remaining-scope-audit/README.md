# Remaining Li EFT Scope Audit

- ID: `li-remaining-scope-audit`
- Status: completed
- Result type: bounded source screening and exact coordinate-matrix certificates
- Working branch: `audit/li-remaining-scope-audit`
- Integration target: `master`
- Integration authorization: user explicitly requested merging into `master`
  at stage 01; Git ancestry records the resulting integration

## Endpoint And Scope

Determine which unverified claims or candidate families in
[arXiv:2201.04639v2](https://arxiv.org/abs/2201.04639v2) can use the existing
formalization, select bounded verification targets, and implement and audit
every recommended target. Candidate count follows the classification; there
is no minimum or maximum quota.
The aim is to test the project's results and reusable interfaces, not to
verify the whole paper or follow every discrepancy into a new proof project.

The six-quark comparison with arXiv:2007.07899v1 is a completed separate
topic. Its remaining sectors and counting polynomials are not investigated
here. Existing comparisons remain the baseline, not new achievements.

## Deliverables And Acceptance

- A source map of the pinned paper's major claim/construction groups, with
  section/equation/PDF locations and a recorded reading depth.
- A candidate matrix classifying selected unverified targets as existing-API,
  small-helper, new-foundation, excluded or unresolved, with source evidence.
- A source-backed selection of targets: proposed statement,
  assumptions, independent coefficient domain, candidate dictionary, reusable
  declarations, missing interfaces, verification gate and stopping boundary.
- Verified proof implementations and persistent axiom audits for every
  recommended target, or an explicitly documented feasibility boundary.
- An explicit classification of deferred targets; an empty selection is valid.

See [the investigation plan](plan.md), [source map](source-map.md),
[candidate classification](candidates.md) and [frozen selection](recommendations.md).
Acceptance requires a defensible
classification and completion of every selected target's proof and audit gates. A source map
is not a theorem-by-theorem coverage denominator or a whole-paper audit.

## Work And Open Obligations

The source-group screening selected three finite algebraic subclaims, not
three new EFT sectors. Implemented: (4.38) explicit inverse and rank six;
(4.41)/(4.44) first-four-row basis certificates and full rank four.
See the [proof dossier](../../proof/current/applications/Physics/LI_BASIS_MATRICES.md).

Literal dipole conventions, general tableau/amplitude construction and software
verification are deferred as recorded in the candidate matrix. The source map
records reading depth; no formula-by-formula paper-wide audit is claimed.

The user permits bounded new foundations or scope refinements at agent
discretion when they preserve existing decisions and do not become a large
project. No such physical/foundational expansion was needed for this selection.

## Result And Verification

`lake build Physics.StandardModel.Operators.Audit.AuditLiBasisMatrices`
passed (3,119 jobs), including 14 strict transitive axiom checks with only
standard Lean axioms. Layout passed (1,092 modules). Links passed (418 Markdown
files, 2,814 links, 100 fragments); `git diff --check` passed.
Full `lake build` passed (6,419 jobs), with no warnings or errors in its log.
All 14 docs/layout regression tests passed. Their first sandbox run failed on
the fixture's nested `git` subprocess (`EPERM`); the unchanged tests passed
when rerun outside that restriction. The three selected candidates have passed
their proof/audit gates; this topic's stopping condition is satisfied.
Pins, allowlists and the root README remain unchanged. The assumptions ledger
and coverage row distinguish proved matrix data from unproved operator identities.

## References

- [Cross-topic coverage ledger](../../verification/li-basis-coverage.md)
- [Coverage reading and maintenance rules](../../verification/README.md)
- [Derivative-free foundations](../derivative-free-completeness/README.md)
- [Common completeness interface](../operator-completeness-interface/README.md)
- [Completed six-quark verification](../li-six-quark-basis/README.md)
- [Workflow](../../architecture/WORKFLOW.md)
