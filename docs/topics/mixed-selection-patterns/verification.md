# Verification

Planning only at base checkpoint 01. No Lean verification baseline is claimed for
this new interface before implementation. The unrelated docs.zip is preserved.

## Implementation — stage 01

- Plan checkpoint 02 froze the zero/nonzero meaning and bounded consumers.
- Focused Physics source build passed 3951 jobs.
- `lake build Math.LinearAlgebra.Audit.AuditMixedSelectionRequests Physics.StandardModel.Operators.Audit.AuditMixedSelectionPatterns`:
  passed 3954 jobs; 22 strict transitive checks (14 Math, 8 Physics).
  Only propext, Classical.choice and Quot.sound are accepted; upper-layer
  imports are rejected. Final focused sources and audits had no warnings.
- Serialized `lake build`: passed 6694 jobs, including registered new audits
  and Math/Physics/GUT aggregates. Existing audit diagnostics were replayed.
- `node tools/layout/check-layout.mjs`: passed 1367 modules.
- `node tools/docs/check-links.mjs`: passed 665 Markdown files, 4109 local
  inline links, 91 fragments, zero errors (final documentation recheck).
- `git diff --check`: passed.

Intermediate elaboration failures were corrected: a redundant rfl after a
closing simp, membership decidability needing explicit target-predicate
unfolding, and a complex-specific negative control in a generic Math module.
The control now works over any field; no dependency, pin, assumption or audit
allowance was changed to resolve these errors.

Statement review checked per-target witnesses rather than union allowance,
conflict only on the same requested domain, explicit degree/symmetry inputs,
and nonzero selected output rather than whole-domain nonzero existence.
BGW uses actual one-copy fields: B1/B2 products over all degrees versus the
fixed-degree charged-Higgs LLHH sector. DGT allowance is IR only; UV prohibition
is kept separate. No generated interaction, matching or rate claim was added.
All new public request/theorem declarations are included in persistent audits.
The unrelated untracked docs.zip was preserved. Stop condition reached;
no master merge or remote push is authorized by this topic implementation.

## Authorized Integration

User-authorized no-ff master merge checkpoint 03 integrates checkpoint 04 and checkpoint 02.
Merged-state full build passed 6694 jobs including 22 strict API checks.
Layout passed 1367 modules; links passed 665 files / 4109 links / 91 fragments;
diff check passed. Topic HEAD is reachable from master, no worktree uses its
branch and no child needs it; local branch deletion is safe. No remote push.
Integration-record edits are documentation-only; no further Lean build needed.
