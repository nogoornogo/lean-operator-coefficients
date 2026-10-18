# Limited generation foundation verification

Working branch `proof/sm-computable-characters`, continuation from `checkpoint 01`.
No merge/push or dependency-pin change. New sources are
`FiniteExteriorExhaustion`, `GenerationExteriorExhaustion` and
`SMGenerationExhaustion`; both existing structural audits and the Math/Physics
aggregates register them. See [results](limited-foundation-results.md) for
the exact theorem scope and remaining original-stage-2 obligations.

## Guarded proof checks

All final builds were serialized with one Lean thread, the unchanged
6 GiB sampled process-group RSS cap, 4 GiB available-memory reserve and
300-second guard. No proof limits were raised. Command template:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/limited-build.log
```

Math and Physics aggregate invocations also set the already used
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`.

| Final build | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| `Physics.StandardModel.Operators.SMGenerationExhaustion` (including both new Math sources) | 4176 jobs, pass | 10.8 s | 4962484 |
| `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport` | 4094 jobs, 122 strict checks, pass | 4.8 s | 5242464 |
| `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport` | 4400 jobs, 210 strict checks, pass | 5.0 s | 5393944 |
| `Math` | 6032 jobs, pass | 5.8 s | 6204792 |
| `Physics` | 5056 jobs, pass | 5.3 s | 5550944 |

Both persistent audits preserve their layer/original-module and numerical
evaluator/certificate import rejection. Their 332 strict transitive checks
permit only `propext`, `Classical.choice` and `Quot.sound`. Final successful
focused/audit/aggregate logs contain no warning or error. Intermediate
elaboration errors and one unused-section-variable warning were corrected
before these checks; they did not require increasing proof limits.

These new theorems use neither the external Weyl premise nor a new literature
premise. Aggregate replays of earlier optional Weyl audits remain conditional.
No retired numerical certificate was restored, built or evaluated. Symbolic
binomial source dimensions are used only through the general nonzero criterion.

## Repository and cache checks

- `node tools/layout/check-layout.mjs`: 1720 modules; layers, imports, cycles,
  aggregate coverage and relocation audits pass.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot hashes
  match; 15 retired modules absent; active imports clean.
- All three new theorem sources contain no `sorry`, custom `axiom`,
  `native_decide`, `implemented_by` or raised heartbeat/recursion setting.

- `node tools/docs/check-links.mjs`: 888 Markdown files, 5516 local links,
  110 heading fragments, zero errors.
- `git diff --check` and `git diff --cached --check`: pass.
- `lake --no-build build Math Physics Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport`:
  exit 0, all targets up to date (6637 jobs).
- Default `lake --no-build build`: exit 3, 7088-job graph, exactly the `GUT`
  aggregate out of date. No other target reports a failure.

The unchanged GUT aggregate previously exceeded this same 6 GiB guard; it is
not recompiled as an unchanged retry here. Thus Math/Physics success must not
be described as a full default `lake build` success.
