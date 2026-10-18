# Heeck–Le structural replacement verification

All Lean checks use one thread through `tools/exact-rank/kernel-probe.py`,
with a 10 GiB sampled process-group RSS guard, 4 GiB host-memory reserve and
300 seconds per invocation. No proof limits or dependency pins were raised.
The old data file's high recursion setting was removed with its evaluated
tables and stepping checker. No custom axiom, incomplete proof, `native_decide`
or audit allowlist exception was introduced.

## Focused checks

| Check | Seconds | Sampled peak KiB | Result |
| --- | ---: | ---: | --- |
| Actual-source quotient connection | 13.3 | 4,485,900 | Uniform twelve-coefficient identity |
| Pair/coupling connections | 29.6 | 4,553,096 | Actual words agree with the block frames and five residual equations |
| Connected literal basis | 12.8 | 4,453,856 | Generated rational presentation and original literal contractions agree |
| Independent structural audit | 4.5 | 4,715,084 | 362 declarations, including private helpers; excluded data/basis imports absent |
| Existing comparison audit build | 8.3 | 4,774,192 | 195 strict transitive checks; original gate/allowlist unchanged |

Intermediate scalar-type inference and elaboration errors and unused-tactic
warnings were fixed before acceptance. Final accepted source builds are clean.
The source derivation is independently audited without importing either the
old Heeck–Le data/basis modules or the Li selected-orbit certificate. A separate
consumer gate checks that retained rational API names point to these derived
maps and that physical consumers retain the actual reconstruction dependency.

## Final full build and fresh audits

The final full default build includes the source and consumer gates. Fresh
sequential audit results and repository checks are recorded below.
Replayed audit messages in a cached build are not fresh executions.

The final default-library build (`lake build GUT`) passed: **7,453 jobs,
10.3 seconds, sampled peak 6,692,264 KiB**, after the focused builds above.
It had no warnings or errors. This is the incremental full build of all
configured targets, not a claimed cold-cache timing.

| Fresh direct audit | Strict checks | Seconds | Sampled peak KiB |
| --- | ---: | ---: | ---: |
| `AuditHeeckLeSixQuarkStructural` | 362 | 3.5 | 4,645,876 |
| `AuditHeeckLeSixQuarkExtraction` | 8 | 3.5 | 4,695,660 |
| `AuditHeeckLeBasis` | 195 | 3.8 | 4,708,916 |

All **565** fresh strict checks passed with the unchanged allowlist
`propext`, `Classical.choice`, `Quot.sound`. Five direct API/source links and
the private-helper dependency traversal also passed. The new source audit
excludes both old Heeck–Le data/basis modules and the Li selected-orbit
certificate; the consumer gate confirms the derived maps are actually used.
Declaration counts are coverage of their current audited sets, not a measure
of mathematical strength against an earlier checkpoint.

Layout passed for 2,067 modules. Retirement checks retain 19 snapshot hashes
and confirm 15 previously retired modules absent with no active imports.
Metadata passed 1,088 portable evidence files; topic coverage passed 146 topics
and 146 outcome links with this ongoing topic's pending exception. Local links
passed 1,096 Markdown files, 6,867 links and 111 heading fragments, with no
errors. The diff and unchanged physical assumptions were reviewed. Whitespace
checks passed before the verified checkpoint. No merge or push is authorized.
