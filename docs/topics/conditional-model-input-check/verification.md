# Verification

Verified at stage 01 on proof/conditional-model-input-check, based on checkpoint 01.
No merge or push is authorized. Build output remains in /tmp.

## Lean checks

Use the existing guarded runner with `LEAN_NUM_THREADS=1`, one serialized
Lean/Lake run at a time, `--rss-limit-gib 10 --min-available-gib 4
--timeout-seconds 300`. No proof option or dependency pin was raised/changed.
Sampled group RSS is not a hard maximum-memory measurement.

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT.Common.ProtonProtection.ConditionalInputChecks /tmp/conditional-input-focused.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 Physics.StandardModel.Operators.BaryonTrialitySMInput /tmp/conditional-triality-final.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT.Common.ProtonProtection.Audit.AuditConditionalInputChecks /tmp/conditional-audit.log
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 10 --min-available-gib 4 --timeout-seconds 300 GUT /tmp/conditional-full.log
```

| Accepted check | Outcome | Elapsed / sampled peak KiB |
| --- | --- | --- |
| Initial neutral-Higgs consumers | 4,728 jobs, exit 0 | 5.3 s / 5,226,316 |
| B3 actual-action source | 3,881 jobs, exit 0 | 7.3 s / 4,854,064 |
| Final consumers and strict audit | 4,911 jobs, exit 0; 43 declarations audited | 8.3 s / 5,300,452 |
| Full default-target `lake build GUT` | 7,369 jobs, exit 0 | 8.3 s / 6,712,080 |

The initial consumer build preceded the P6 dictionary lemma; the final audit
build includes it. All new named declarations and selected reused model
certificates are strictly transitively audited. Only propext, Classical.choice
and Quot.sound are allowed. Source/import aggregation is registered in Physics
and GUT. Both aggregates rebuilt. Accepted build logs have no warnings/errors.
The first B3 build failed on an orphaned documentation comment; it was corrected
before the accepted build. This was a syntax failure, not a negative model verdict.

## Exact supplementary checks

All use Python standard-library rational/integer arithmetic, no new environment.
They supplement Lean and are not theorem premises or UV-model certifications.

- `python3 tools/conditional-model-input-check/check_inputs.py`: pass; DFPW
  72 cover elements, B-L normalization, B3/P6 components/charged-Higgs and Ma
  parity controls. The script documents its restricted domain in its module header.
- `python3 tools/proton-protection-model-checks/audit_models.py`: 7 tests passed.
- `python3 tools/species-surplus-model-checks/audit_models.py`: 5 tests passed.
- `python3 tools/su6-twisted-protection/check_s3_qque_tensor.py`: 3 tests passed;
  exact ordered/symmetric counts 9/0 and 18/18.
- `python3 tools/s3-yukawa-compatible-qque/check_sample.py`: pass; 486 invariant,
  81 symmetric cases, witness 1 and missing-sign control -1.
- `python3 tools/su6-twisted-protection/audit_block_phase.py`: 6 tests passed.

## Documentation and review

`node tools/layout/check-layout.mjs`: pass, 1,983 modules. Local links: pass,
1,025 Markdown files, 6,202 local links and 116 heading fragments, zero errors.
`git diff --check`: pass. The final review
compares actual theorem statements, the model-source boundary matrix,
reader-facing studies and both assumption ledgers. In particular subgroup
allowance is not full-group allowance; three-copy minima are conditional on
three copies, and B3/P6 use charged Higgs rather than a neutral replacement.
Root README, dependency pins, unrelated user docs.zip and other worktrees are
untouched. Full UV-admission, loop/matching, physical rates and new foundations
were not required to close this bounded one-pass endpoint.
