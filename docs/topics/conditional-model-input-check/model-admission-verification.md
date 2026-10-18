# Concrete model-admission recheck verification

Checked at stage 01 on proof/conditional-model-input-check, following checkpoint 01.
The source comparison is documented reading, not a Lean proof of a paper.
Model-level failures/missing premises remain distinct from successful Lean checks.

## Focused checks

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT.Common.ProtonProtection.LRModelAdmissionControls /tmp/bl-lr-model-controls.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT.Common.ProtonProtection.Audit.AuditBLLRModelAdmission /tmp/bl-lr-admission-audit.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT /tmp/bl-lr-admission-full.log
```

- Focused source: exit 0, 5.0 seconds, sampled group peak 5,184,144 KiB.
- Persistent audit: exit 0, 4,738 jobs, 5.5 seconds, sampled peak 5,181,432 KiB;
  all eight new control theorems and four reused bridge endpoints passed the
  12 strict transitive checks. Only propext, Classical.choice and Quot.sound
  are allowed. No custom axiom, sorry or audit exception.
- Full GUT/default-target: exit 0, 7,374 jobs, 6.8 seconds, sampled group
  peak 6,704,028 KiB. Final accepted logs have no warnings or errors.

The named source contracts were reread: conventional comparison in
1411.5042v2 introduction pp.1–3; LR 1507.01584v3 Section II Eqs.(1)–(3) and
footnote 1. The source-to-premise table is the authoritative applicability
result; successful builds do not turn unprovided potential data into premises.
The controls are quadratic operators, not full potential/VEV realizations.
No further Python oracle is needed for these kernel-checked operator identities.

All runs are serialized under unchanged one-thread, 300-second, 10 GiB sampled
RSS and 4 GiB host-reserve guards. No dependency/proof-limit changes. Disposable
output is in /tmp. Root README, other worktrees and unrelated docs.zip are untouched.

Layout check passes for 1,988 modules. Local links pass: 1,031 Markdown files,
6,230 links, 116 heading fragments, zero errors. `git diff --check` passes.
Final record-only edits do not require a new Lean build.
