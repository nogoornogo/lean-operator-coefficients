# Literature links for current results

- ID: literature-linking
- Status: completed
- Result type: bibliographic linkage and scoped related-work comparison
- Working branch: docs/literature-linking
- Integration target: master; local merge authorized; push not authorized
- Authorization: user supplied a ChatGPT literature survey and requested missing
  references be added to existing documentation, including already studied sources.

## Endpoint and plan

1. Inventory the 19 distinct supplied references against current dossiers,
   topic source registers and coverage ledgers.
2. Check primary bibliographic records, abstracts and the specific accessible
   locations needed to explain a reference. Correct supplied titles/links.
3. Add missing point-of-use references to existing result guides and dossiers.
   Link existing comparisons rather than duplicating them or upgrading their scope.
4. Record each source's destination and evidence depth. Separate background,
   related methods, actual bounded certificates and explicit external premises.
5. Run metadata, topic-index, local-link and diff checks; review and commit.

No Lean source, proof premise, dependency or selected root README claim changes.
No software is installed/executed and no new literature-basis proof is attempted.
Publisher abstracts/contents establish only their stated scope, not a proof
of equivalence to the repository. Do not infer novelty, priority, a complete
search, mathematical dependence or whole-paper verification from this survey.
Publication years and pinned source versions are citation metadata; work dates
and local Git IDs do not belong in documents.

## Stop and verification

Stop when every supplied source is either linked at a relevant existing entry
point or explicitly limited to an optional conceptual analogy. An inaccessible
full text is not a reason to claim detailed checking or to start new foundations.
Run python3 tools/docs/check-work-metadata.py, topic coverage with this topic
explicitly pending, node tools/docs/check-links.mjs and git diff --check.
No Lean build or axiom audit is rerun for documentation-only changes.
Untracked docs.zip is user-owned and remains untouched. The user subsequently
authorized the local merge; no push is authorized.

## Result

Completed all 19 source dispositions: reused 12 existing bibliographic links,
added seven previously unlinked sources at their points of use, and corrected
two preprint-version links. The [literature map](../../proof/RELATED_LITERATURE.md)
records relevance without upgrading background to a proved comparison.
See [results and verification](results.md) for inspection depth and boundaries.
The user subsequently authorized local integration into master.

## Scoped comparison findings

The user subsequently requested a synthesis of the three literature findings,
including one retained proof branch. Read the owning integrated records and
branch documents without merging/copying branch proofs. The
[findings summary](../../verification/literature-findings.md) separates exact
flavor boundaries, fixed-reading normalization and conditional branch-only
coefficient comparison. This adds no proof or verified-coverage row and does
not authorize author contact, a separate erratum, merge or push.

## Authorized integration follow-up

The user requested this branch be merged first, followed by the retained
Dev–Mohapatra proof branch. After its proof checks, rewrite the findings page
as a result summary without branch/integration status prose; keep source
adoption and normalization conditions. Record integration evidence in the
owning topics rather than the findings page. No push or author contact.

See [local integration verification](master-integration.md) for the authorized
merge and combined verification record.
