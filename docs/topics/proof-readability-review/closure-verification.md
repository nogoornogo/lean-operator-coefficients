# Verification of the structural continuation

This closes the bounded review endpoint, including an explicit E6 foundation
stop. It does not claim repository-wide elimination of finite arithmetic or
all numerical certificates.

Earlier verified replacements and their strict audits are recorded in the
[Li verification](source-replacement-verification.md),
[Heeck–Le verification](heeck-replacement-verification.md) and
[finite-index result](finite-index-replacement.md). Their earlier successful
checks are not described as fresh reruns in this final rank checkpoint.

The final rank sources preserve the six example rank statements and the
rank/field-transport/nullity API. The constructor adds only the three explicit
linear reconstruction obligations. No physical assumptions, custom axioms,
proof-limit increases or dependency changes were introduced. The E6 review
changes documentation only and leaves its existing checks in place.

Commands use one Lean thread, a sampled process-group RSS limit of 10 GiB,
a 4 GiB host reserve and a 300-second invocation timeout:

```
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build Math.LinearAlgebra.Audit.AuditExactRankCertificates /tmp/rank-final-audit-build.log --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build GUT /tmp/readability-final-full.log --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py Math/LinearAlgebra/Audit/AuditExactRankCertificates.lean /tmp/readability-final-fresh-audit.log --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300
```

The focused build passed in 6.8 seconds, sampled peak 4,568,680 KiB,
with no warnings. Its 13 strict transitive roots include all twelve earlier
roots and the new action constructor. The allowlist remains exactly `propext`,
`Classical.choice`, `Quot.sound`. The Math layer gate is retained.

The full default build passed all 7,453 jobs in 14.8 seconds after focused
builds, sampled peak 6,700,448 KiB, without warnings. The fresh direct audit
passed all 13 roots in 3.3 seconds, sampled peak 4,503,432 KiB.

Repository checks passed: layout (2,067 modules), retired certificates
(19 snapshot hashes and 15 retired modules absent), portable metadata,
topic navigation/outcomes, local links and `git diff --check`. The new settled
continuation outcome starts the next history volume because the previous volume
had reached its 30-entry limit. No checker or audit gate was relaxed.
