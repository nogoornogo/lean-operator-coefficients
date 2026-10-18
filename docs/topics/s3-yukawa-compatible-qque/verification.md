# Verification

Verified at stage 01 on proof/s3-yukawa-compatible-qque, based on
checkpoint 01. No integration is authorized.

## Lean

The initial source-only check used
`timeout 300 lake env lean -j1 Physics/StandardModel/Operators/S3YukawaCompatibleQque.lean`
and passed before the final Higgs and dictionary aliases were added. The
following final focused build covers those additions and the persistent audit:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 Physics.StandardModel.Operators.Audit.AuditS3YukawaCompatibleQque /tmp/s3-yukawa-focused.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT /tmp/s3-yukawa-full.log
```

- Focused: exit 0, 3,637 jobs, 7.8 s; sampled group peak 4,688,952 KiB.
- Persistent audit: all 25 explicitly registered new declarations pass strict
  transitive axiom checks. Only propext, Classical.choice and Quot.sound are
  permitted; no audit exception or custom axiom is introduced.
- Full `lake build GUT`: exit 0, 7,366 jobs, 8.5 s; sampled group peak
  6,713,148 KiB. GUT is the package's default target, so this is the full
  default project build. Both Physics and GUT aggregates rebuilt.
- No warnings or errors in either accepted build log. Lean/dependency pins and
  proof limits are unchanged. Runs are serialized with one Lean thread,
  300-second timeout, 10 GiB sampled group RSS cap and 4 GiB host reserve.
  Sampled RSS is not a hard maximum-memory measurement.

## Other acceptance checks

- `python3 tools/s3-yukawa-compatible-qque/check_sample.py`: pass; 486 exact
  invariant basis cases, 81 symmetric cases, witness 1, missing-sign control -1.
- `node tools/layout/check-layout.mjs`: pass; 1,980 modules, including source
  and audit aggregate registration, layer/import/cycle/relocation checks.
- `node tools/docs/check-links.mjs`: pass after the verification record was
  created; the first run correctly detected its then-missing link target.
- `git diff --check`: pass.

Final source/diff review confirms the same field dictionary in flavor-map and
qque statements, the existing physical exterior transport, explicit neutral
Higgs and independent gauge/flavor assumptions, and the documented Yukawa/UV
boundaries. Root README and unrelated docs.zip are untouched. No fallback,
external literature premise, new dependency, merge or push was used.
