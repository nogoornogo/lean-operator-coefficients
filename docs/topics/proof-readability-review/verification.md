# Readability pilot verification

This is an earlier partial checkpoint. The completed Li source/orbit
replacement is recorded in [the current result](source-replacement-results.md)
and [its verification](source-replacement-verification.md).

## Scope

The new `LiSixQuarkProbeDecomposition` proves an explicit splitting of the
local array into the probe kernel and the normalized extra line, uniqueness
of that decomposition and the 24-dimensional kernel result. It imports no
dense Li finite-data module. The existing `printed_finrank` reuses the kernel
dimension lemma; its printed-span equality still depends on the old basis.
The complex `right_inverse` theorem is derived from `left_inverse` by the
general finite-square-matrix theorem. All original result statements are kept.

`LiSixQuarkFiniteData` is byte-identical to the branch's starting version.
Its attempted rewrite stopped under the existing resource guard and was
reverted. No numerical certificate or old theorem was deleted or weakened.
No retired numerical module was built. No dependency pin, proof limit or audit
allowlist changed.

## Commands and bounded checks

All bounded Lean invocations use `LEAN_NUM_THREADS=1` and
`python3 tools/exact-rank/kernel-probe.py` with `--rss-limit-gib 10`,
`--min-available-gib 4` and `--timeout-seconds 300`.

- Direct check of the new decomposition: passed, 4.3 seconds, sampled peak
  4,259,740 KiB.
- Initial focused decomposition audit build: passed, 3,279 jobs, 12.5 seconds,
  sampled peak 4,631,676 KiB; five strict transitive checks.
- Initial flavor-boundary consumer build: passed, 3,311 jobs, 18.5 seconds,
  sampled peak 4,657,168 KiB; thirteen strict checks. This preceded the later
  consumer-side inverse simplification; final downstream checks are separate.
- Fresh direct decomposition audit: passed, five strict transitive checks,
  5.8 seconds, sampled peak 4,547,236 KiB.
- Attempted direct finite-data rewrite: resource-stopped at 110.3 seconds,
  sampled peak 10,492,236 KiB; reverted without increasing the budget.
- The proposed general square-matrix implication was independently checked
  in a disposable Lean example; it is not a new mathematical assumption.

Final focused/downstream checks and full-build evidence are recorded below.
No merge or push is authorized.

## Retained milestone focused check

After reverting the monolithic finite-data edit, the build of
`Physics.StandardModel.Operators.Audit.AuditLiSixQuarkBasis` passed:
3,300 jobs, 77.4 seconds, sampled peak 4,820,144 KiB. It rebuilt the
consumer-side inverse theorem and local basis/residual consumers, then passed
all eighteen existing strict axiom checks. The original statements and
actual-field scope remain unchanged.

## Full-build and repository checks

The final default-target `--build GUT` check passed: 7,417 jobs, 62.1 seconds,
sampled peak 6,648,672 KiB, no warnings or errors. This builds the final retained
source tree, including the revised printed-span/flavor-boundary consumers and
both aggregates. Replayed audit messages in this build are not presented as
fresh audits; the separate direct checks below provide fresh evidence.

Layout passed for 2,031 modules. The retired-certificate checker passed all
19 snapshot hashes and confirmed 15 retired modules absent with no active
imports. Documentation checks passed: 1,079 portable evidence files, 146 topics
with 146 outcome links, 1,087 Markdown files, 6,807 local links and 111 heading
fragments without errors. Whitespace checks passed.

This settles an unmerged, bounded partial result. It does not complete the
full replacement plan. The resource stop is recorded without changing the
statement, proof limits, trust assumptions or verification acceptance policy.

## Final fresh transitive audits

Each audit was run directly with `lake env lean` through the bounded runner,
sequentially after the full build. All passed with the unchanged axiom allowlist:

| Audit | Strict checks | Seconds | Sampled peak KiB |
| --- | ---: | ---: | ---: |
| `AuditLiSixQuarkProbeDecomposition` | 5 | 4.0 | 4,590,972 |
| `AuditLiSixQuarkBasis` | 18 | 3.8 | 4,606,640 |
| `AuditLiSixQuarkFlavorBoundary` | 13 | 4.0 | 4,613,032 |

Total: 36 fresh checks. The pilot audit also rejects imports of the dense Li
data and basis modules, preserving its independent dependency boundary.
