# README and result-guide reorganization

## Authorized plan and endpoint

The user specified eight README sections: overview, general theorems, decidable
structural classifications, reverse input constraints, concrete model inputs,
independent results, build link and Apache 2.0 license. Representative formulas
and short explanations belong in README; detailed conditions belong in five
linked category guides. The user also authorized deletion of subjects.

1. Inspect the existing subject indexes and preserve their dossier destinations.
2. Simplify root README and create the three missing category guides.
3. Expand the existing model and independent-result guides; shorten the result map.
4. Delete the four subject index files, redirect incoming links and update policy.
5. Check navigation, preservation and diff; commit on the existing topic branch.

No Lean statements, assumptions, source files, aggregates or dependency pins
are changed. No theorem-level extension, merge or push is part of this task.

## Result

Root README now follows the eight agreed sections with representative formulas.
GENERAL_THEOREMS, DECIDABLE_CLASSIFICATIONS and INPUT_CONSTRAINTS are new;
APPLICATION_GUIDE and RETAINED_RESULTS supply the other two category entrances.
RESULTS_AND_SCOPE is a short routing page. Role indexes retain unique dossier
links from the deleted subject indexes. Current workflow and dossier placement
rules describe the new structure. The retained dashboard receives link-target
updates only; historical descriptions of the previous organization stay intact.

The root formulas are summaries. Category guides retain fixed-input scope,
derivative-free minimum boundaries, the finite-domain versus arbitrary-modulus
distinction and explicit unresolved model premises. The selected S3 sample is
an allowed qque coefficient, not full model or Yukawa realization.

## Verification

Run:

```sh
python3 tools/docs/check-topic-index.py --pending-topic proof-scope-and-application-guide
node tools/docs/check-links.mjs
git diff --check
```

The subject-index dossier links were verified against the role indexes at
this checkpoint. Later snapshot-only checks are recorded in the
[current verification](snapshot-documentation-verification.md).
All 47 former subject-index dossier links were checked against the role indexes.
The first link check correctly reported this verification record before it
was written; the final check includes the completed record.

No Lean build or axiom audit was rerun: this is documentation-only and creates
no new proof verification baseline. The untracked user-owned docs.zip is
untouched. No master merge or remote push was performed.

## Shared review follow-up

Accepted the three small README suggestions from the supplied ChatGPT review:
restore visible all-degree charge selection, define k/q/l and L beside the
fixed-SM congruence, and distinguish allowed coefficients from generated
interactions and decay rates in the overview. The eight sections and five
detailed guides remain unchanged. The README is now 103 lines.

Reran the local link check and git diff --check successfully. The link check
still reports 1,060 Markdown files, 6,647 local links, 107 heading fragments
and zero errors. No Lean build or axiom audit was rerun for this prose-only
follow-up. No merge or push was performed; docs.zip remains untouched.
