# Verification

Base master checkpoint 01 follows mixed API merge checkpoint 02, verified with full build
6694 jobs, 22 strict API checks, layout 1367 modules and links
665 files / 4109 links / 91 fragments. This is not a new-consumer proof baseline.

## Implementation — stage 01

- Scope/plan checkpoint: checkpoint 03, before proof implementation.
- Focused consumer source build: passed 3952 jobs.
- `lake build Physics.StandardModel.Operators.Audit.AuditDgtQuarticityMixedRequests`:
  passed 3954 jobs, 14 strict transitive checks over new public declarations.
  Only propext, Classical.choice and Quot.sound allowed; upper-layer imports
  rejected. New source and audit builds had no warnings or elaboration failures.
- Serialized `lake build`: passed 6696 jobs, including the registered audit
  and Physics/GUT aggregate builds. Existing audit diagnostics were replayed.
- `node tools/layout/check-layout.mjs`: passed 1369 modules.
- `node tools/docs/check-links.mjs`: passed 669 Markdown files, 4128 local
  links, 91 fragments, zero errors (final documentation recheck).
- `git diff --check`: passed.

Statement/source/dossier/assumptions/coverage review retained: DGT uses the
same Z9 IR dictionary for the positive mixed request, each allowed selector
has its own nonzero output witness, and the Circle UV negative control is a
different action. Quarticity keeps SM-only, bare and eta-dressed domains
separate, with the original one-copy complexified-real-eta scope. Opposite
requests on the dressed domain are inconsistent; its nonzero witness also
independently refutes prohibition. No full extended-alphabet or generated
interaction result is inferred.

No sorry, custom axiom, dependency/pin change or audit allowance exception was
introduced. No generic API changes or new physical premises were necessary.
The existing literature comparisons are unchanged; coverage gained evidence
links for the repackaged requests. The unrelated docs.zip remains untouched.
The bounded endpoint is reached; this new topic is not merged or pushed.

## Master Integration (stage 01)

The child was merged into the parent at `checkpoint 04`, then the parent into
master at `checkpoint 05`, with explicit user authorization and `--no-ff`.
Merged-state `lake build` passed (6700 jobs), including the 14-declaration
DGT/quarticity and 53-declaration non-SUSY strict transitive audits.
Layout inspection passed (1373 modules); local links and `git diff --check`
passed. The subsequent integration-record edits are documentation-only;
no additional Lean rebuild is required for those edits. Git identity was
missing on the first merge attempt; command-local identity completed the
merges without repository/global configuration changes. No conflicts,
remote push or changes to the untracked `docs.zip` or other worktree.
