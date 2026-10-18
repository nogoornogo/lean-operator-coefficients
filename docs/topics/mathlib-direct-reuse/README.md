# Direct Mathlib Reuse And Provenance Review

- ID: mathlib-direct-reuse
- Status: completed
- Result type: verified refactoring and bounded reuse review
- Working branch: `refactor/mathlib-direct-reuse`
- Integration target: `mistral-vibe` (bounded child, not a merge of E6 into master)
- Integration evidence: Git ancestry into the recorded target

## Endpoint And Scope

Replace the adapted projection proof in `BasedLieComparison` by a direct call
to the pinned mathlib helper. Preserve theorem types, assumptions, generator
equations, dependency pins and the existing E6 verification boundary.

The adjacent API review also found the existing public TauCeti root-space
dimension formula with the same assumptions. Replace `RootSpaceDimension`'s
independent proof with that theorem and a finite-cardinality conversion.
This uses the already pinned package, not a new package or revision.

Review other project Lean sources for explicit port/adaptation notices and
substantial exact proof-text overlap with pinned mathlib/TauCeti. Inspect
candidates, distinguishing library calls, mathematical similarity and actual
maintained copies. This is a bounded engineering review, not a legal audit or
a claim of detecting every unattributed/renamed derivation.

## Deliverables And Acceptance

- Direct helper reuse with unchanged public comparison API.
- Generic regression examples without source simplicity and the existing
  actual E6/D5 comparisons; unchanged strict axiom allowlist.
- Focused audit, full `lake build`, document link and diff checks.
- Corrected implementation/upstream documentation and recorded review findings.
- Preserve existing attribution/license notices; do not infer relicensing from
  removal of a proof body or select a repository-wide license.

## Result And Verification

- Initial mathlib-only replacement: focused 3802 jobs / 41 strict axiom checks;
  full `lake build` passed, 5517 jobs.
- Both replacements: focused 3815 jobs / 41 strict axiom checks; no warnings
  in the changed modules. Generic regression examples retain the absence of
  source simplicity and do not impose algebraic closedness on the dimension lemma.
- Final `lake build`: passed, 5530 jobs, including the persistent downstream
  audits. Additional jobs come from newly imported modules in the existing
  pinned TauCeti package. Existing warnings remain elsewhere; changed modules
  are warning-free. No package pin, audit allowlist, public theorem type or
  physical assumption has changed.
- `node tools/docs/check-links.mjs` and `git diff --check`: passed.
- No implementation obligations remain in this bounded topic. The internal
  mathlib API dependency and provenance-review limitations remain documented;
  repository-wide licensing and broader deduplication are not claimed resolved.

## References

Subsequent maintenance: the user later approved removing the retained local
license notice/text. See [that separate topic](../../architecture/DISTRIBUTION.md).
The acceptance criteria above describe this earlier refactoring checkpoint.

- [Comparison source](../../../Math/LieAlgebras/BasedLieComparison.lean)
- [E6 comparison dossier](../../proof/current/inputs/Math/E6_GECK_COMPARISON.md)
- [Upstream policy](../../architecture/UPSTREAMING.md)
- [Horizontal review and its limits](REVIEW.md)
