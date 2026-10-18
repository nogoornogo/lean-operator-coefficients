# Graded Completeness: Six-Quark And LLHH Regressions

- ID: graded-sector-regressions
- Status: completed
- Result type: proved consumer equivalences and commuting comparison diagrams
- Working branch: `proof/graded-sector-regressions`
- Integration target: `master`
- Integration evidence: Git ancestry in `master` is authoritative; the working branch name is retained as a historical record

## Endpoint And Scope

Connect degree-uniform quotient completeness to two independently defined
physical coefficient sectors: specified all-right `u²d⁴` (dimension nine,
mixed degree `(6,0)`) and Weinberg `LLHH` (dimension five, `(2,2)`).
These are application regressions, not missing cases of the general theorem.
LLHH tests multiple boson slots, not multiple Higgs-doublet species or a new
high-dimension classification.

Keep arbitrary abstract residual groups and arbitrary complex fermion
multiplicity modules. Up/down carriers remain distinct. The LLHH comparison
uses the existing single Higgs doublet with trivial residual action; it does
not silently enlarge the old symmetric-flavor Hom result.

## Deliverables And Acceptance

See [the staged plan](plan.md). Both sectors must have proved input/action and
support dictionaries, generic quotient equivalences, and comparison with the
existing residual targets. Extraction/reconstruction diagrams, both inverse
laws and zero/nonzero iff must be checked, including their normalizations.
The six-quark target is the typed exchange-constrained residual Hom, not
25 unrestricted coefficients or two coefficients at arbitrary multiplicity.

## Work And Open Obligations

All A–D acceptance gates passed: action/input dictionaries, both consumers,
comparison diagrams, inverse laws, zero/nonzero conditions, one-generation
controls, strict audits, full compatibility build and documentation checks.
There are no remaining tasks within this topic's frozen scope. See
[results](results.md) and [interfaces](interfaces.md).

Work stops at these two fixed-content consumers. The old six-quark finite
flavor-basis inverse has been replaced by tensor lifting; no new physical
assumption or substantial foundational project was required. Dimensions eight
through eleven and unrelated field contents remain outside this topic.

## Result And Verification

The prerequisite `DeltaBTwoFlavorBridge` rebuild passed 3,287 jobs, with no
finite-dimensionality needed in its inverse construction. Both consumer builds
and 41 strict transitive audit checks passed (3,839 combined jobs).
The final full build passed 6,524 jobs without warnings. Layout checks passed
1,197 modules; Markdown checks passed 460 files / 3,081 links / 100 fragments;
`git diff --check` passed. See [results](results.md).
The earlier planning commit was documentation-only and did not rerun Lean.
The proof checkpoint is `checkpoint 01` and the verified completion commit is `checkpoint 02`.
Master integration was explicitly requested at stage 01.

## References

- [General theorem and scope](../../proof/current/core/Math/GRADED_OPERATOR_COMPLETENESS.md)
- [Six-quark connection dossier](../../proof/current/applications/Physics/GRADED_SIX_QUARK_COMPARISON.md)
- [LLHH connection dossier](../../proof/current/applications/Physics/GRADED_WEINBERG_COMPARISON.md)
- [Existing actual SM comparison](../../proof/current/applications/Physics/GRADED_BNV_COMPARISON.md)
- [Six-quark model interface](../delta-b-two-model-interface/README.md)
- [Six-quark literature certificate](../../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md)
- [Weinberg certificate and hypotheses](../../proof/current/applications/Physics/LI_WEINBERG_BASIS.md)
