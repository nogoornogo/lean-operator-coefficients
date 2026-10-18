# Signed mixed-lepton verification

Continuation from `checkpoint 01`, branch `proof/sm-computable-characters`.
The [result](mixed-lepton-results.md) is a proved actual subfamily, not
completion of the general colored q/l endpoint. No merge or push.

## Guarded proof checks

Builds are serialized, one Lean thread, 6 GiB sampled process-group RSS cap,
4 GiB available-memory reserve, 300-second guard, default Lean proof limits:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/mixed-check.log
```

| Check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| `Physics.StandardModel.Operators.SMLeptonMaximalLocal` | 4379 jobs, pass | 5.3 s | 5089216 |
| `Physics.StandardModel.Operators.SMMixedLeptonSupport` (including charged coupling, statistical gluing, dictionaries) | 4391 jobs, pass | 11.3 s | 5095128 |
| Math structural audit | 4108 jobs, 187 strict checks, pass | 5.0 s | 5235492 |
| `SMMixedLeptonWord` and Physics structural audit | 4417 jobs, 241 strict checks, pass | 7.8 s | 5411424 |
| Math aggregate | 6043 jobs, pass | 6.3 s | 6208760 |
| Physics aggregate | 5070 jobs, pass | 6.3 s | 5556652 |

The labelled concrete-carrier transport initially reached the default
heartbeat limit. Moving label transport into a generic `allowed_at` lemma
before specialization removes the expensive elaboration; the statement,
logical assumptions, resource guard and Lean proof limits are unchanged.
Other intermediate elaboration/arithmetic errors were corrected, without
changing the endpoint predicate. No retired numerical proof was built.

The two structural audits total 428 strict transitive checks, allowing only
`propext`, `Classical.choice` and `Quot.sound`. Layer/origin and numerical
import rejection are unchanged. Final successful logs have no warnings.
The aggregate invocations also set `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, with the same guard.

## Repository checks

- Layout: 1737 modules; layer/import/cycle/aggregate/relocation checks pass.
- Local links: 894 Markdown files, 5560 inline links, 110 fragments, zero errors.
- Retired-certificate checker: 19 hashes match, 15 retired modules absent,
  active imports clean.
- All seven new theorem modules contain no `sorry`, custom `axiom`,
  `native_decide`, `implemented_by`, diagnostics or raised proof limits.
- Root README, dependency pins, retired sources and numerical CSVs unchanged.

- `lake --no-build build Math Physics Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport`:
  exit 0; all 6654 jobs up to date.
- Default `lake --no-build build`: exit 3; 7105-job graph with exactly the
  unchanged `GUT` aggregate stale. Its known resource boundary is not
  retried; this is not a full default-build pass.
- Final link and `git diff --check` checks pass. Both source aggregates and
  both persistent audits have successful guarded builds; no source change
  follows those builds.

## User-requested full build recheck (stage 01)

At `checkpoint 02`, the user explicitly requested a full compilation including
`GUT.lean` after retiring the numerical certificates. The earlier untested
GUT boundary above is superseded by this successful recheck.

```sh
env LEAN_NUM_THREADS=1 MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0 lake build
```

A temporary runner reused the existing `kernel-probe.py` process-group RSS,
host available-memory and signal helpers to monitor this exact default
command. For this aggregate recheck the sampled RSS cap was 10 GiB, with a
4 GiB host reserve and 300-second timeout. Lean options, dependency pins,
sources and the default Lake target were unchanged.

- Exit 0, 7105 jobs; `GUT` was actually rebuilt in 3.1 seconds.
- Whole invocation: 6.8 seconds; sampled process-group peak 6581232 KiB
  (about 6.28 GiB). No guard interruption, warnings or errors.
- The measured peak exceeds the earlier 6 GiB guard. This run establishes
  that the current aggregate builds within the stated larger guard; it
  does not establish the exact cause of an earlier interruption.
- Retired-certificate checker rerun: 19 snapshot hashes match, 15 retired
  modules absent, active imports clean. No retired numerical certificate
  was built.

This updates build verification only. The general colored/mixed support
classification remains open; no new theorem or external input was added.
