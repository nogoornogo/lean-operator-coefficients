# Remaining numerical certificate retirement

The user explicitly directed that old numerical proofs never be built again.
After `checkpoint 01`, `SMComputableCharacterExamples` and `SMNeutralSparseExamples`
were removed as active Lean sources and from the Physics aggregate. Their
byte-identical text snapshots and the two former audit snapshots are in the
[source archive](archive/remaining-numerical/README.md), with source commit and
SHA-256 hashes. The existing thirteen Q18 numerical sources remain retired.

The active symbolic audits keep their layer and strict transitive standard
axiom checks. They retain the full symbolic evaluator-correctness and
conditional-consumer endpoints (26 computable and 48 sparse checks); entries
for retired closed-example declarations are archived with those sources.
Structural audits additionally reject both retired example-module names.
No axiom allowlist or acceptance policy was relaxed.

`python3 tools/exact-rank/check-retired-certificates.py` checks 19 snapshot
hashes, 15 retired modules absent from source, and no active import of those
modules. A separate byte comparison with `git show <recorded-commit>:<path>`
confirmed all 19 snapshots against their recorded Git source commits. The
checker never invokes Lean or asserts a numerical equality. Generic evaluators,
small weight-dictionary checks and structurally derived basis dimensions remain
available; no closed multiplicity/rank example is a build/cache prerequisite.

All Lean commands used `LEAN_NUM_THREADS=1`, the existing 6 GiB sampled group
threshold and 4 GiB host reserve, serialized through `kernel-probe.py`:

| Target | Result | Seconds | Sampled group peak KiB |
| --- | --- | ---: | ---: |
| `AuditSMComputableCharacter` | passed, 26 strict checks | 5.0 | 5402764 |
| `AuditSMSparseCharacter` | passed, 48 strict checks | 5.0 | 5418252 |
| `AuditSMStructuralSupport` | passed, 78 strict checks | 5.0 | 5374196 |
| `Physics` aggregate | passed, 5015 jobs | 5.5 | 5575608 |

The guarded full `GUT` build stopped at 5.3 s with sampled process-group RSS
6324252 KiB, slightly above the unchanged 6 GiB threshold. No retired module
was a target and no closed numerical proof was run. This is a resource stop,
not full-build success. The remaining aggregate frontier is inspected before
further proof work; full-build acceptance remains outstanding at this checkpoint.
The user also authorized the [signed/mixed continuation](signed-mixed-plan.md).

The final no-build frontier contains only `GUT` (exit 3); all retired numerical
modules are absent from the active graph. Layout passed for 1680 modules.
Links passed for 872 Markdown files, 5392 local links and 109 fragments, zero
errors (same read-only checker retried for sandbox `git ls-files` EPERM).
`git diff --check` passed. This is a verified retirement checkpoint with the
root aggregate resource gate still open, not a new full-project baseline.
