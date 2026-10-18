# B-L / LR continuation verification

Verified stage 01 on proof/conditional-model-input-check, following the
checkpoint 01 ten-candidate checkpoint. No merge/push authorization is implied.

## Lean

Final focused source/audit and full default-target builds were serialized with
the unchanged one-thread, 300-second, 10 GiB sampled group RSS and 4 GiB
host-reserve guards:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT.Common.ProtonProtection.Audit.AuditBLLRInputBridges /tmp/bl-lr-audit.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT /tmp/bl-lr-full.log
```

- Final focused/audit build: exit 0, 4,737 jobs, 19.8 seconds, sampled group
  peak 5,307,040 KiB. Both bridge sources rebuilt.
- Persistent audit: 48 new named abbreviations, definitions and theorems pass
  strict transitive checks with only propext, Classical.choice and Quot.sound.
- Full GUT (default target): exit 0, 7,372 jobs, 6.3 seconds, sampled group peak
  6,701,656 KiB. New audit replayed and GUT aggregate rebuilt.
- Accepted final logs contain no warnings/errors. No custom axioms, sorry,
  heartbeat increases, audit exceptions or dependency changes.

Intermediate focused elaborations corrected nsmul/finite-character rewriting,
Circle-unit coercions, API names, unfolding of product representations and a
dependent kernel-membership rewrite. One unused simp argument was removed.
These were implementation diagnostics, not negative physical/model verdicts.
No resource guard fired and no new theorem-level foundation was required.

## Other checks and assumption review

- `python3 tools/conditional-model-input-check/check_inputs.py`: pass. This is
  the existing exact input-normalization control, not a proof of the new kernel
  equivalence; that result is independently kernel-checked in Lean.
- `node tools/layout/check-layout.mjs`: pass; 1,986 modules, layers/imports,
  cycles and aggregate coverage checked.
- `node tools/docs/check-links.mjs`: pass; 1,028 Markdown files, 6,219 local
  links, 116 heading fragments and zero errors. `git diff --check`: pass.

Reviewed statements retain the exact model boundaries: Circle stabilizer
rather than a faithful quotient/full LR stabilizer; explicitly constructed
SM representations rather than a discovered UV fermion mass radical; the
specified quadratic-coordinate hypothesis rather than a derived LR potential.
The actual LR-restricted bidoublet action agrees with the transported complete
light-kernel action and its dual, not merely an abstract isomorphic vector
space. The conditional B1 witness remains a subgroup witness.

Disposable logs are outside version control. Root README, user docs.zip and
other worktrees are unchanged. Final record-only edits require link/diff checks,
not another Lean rebuild or a new proof baseline.
