# Structural classification verification

Work resumes at `checkpoint 01` on `proof/sm-computable-characters`. Eight new
theorem modules are registered in the existing Math/Physics aggregates.
No new dependency, proof premise or numerical certificate is introduced.

## Guarded Lean checks

All builds are serialized, use the unchanged default Lean proof limits and
the existing guard:

```sh
LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/structural-MODULE.log
```

The timeout remains 300 seconds. RSS is sampled across the child process
group; it is a diagnostic guard, not a proof input or a hard cgroup limit.
No retired certificate, closed character calculation or numerical evaluator
was restored, executed or used in these proofs.

| Check | Result | Time | Sampled group peak (KiB) |
| --- | --- | --- | --- |
| `SMMixedWeakCapacity` including `ContentTorusBound` | passed, 4349 jobs | 18.5 s | 5071676 |
| `ContinuousLineActions` | passed, 3996 jobs | 4.8 s | 4858276 |
| `SMSaturatedContentSupport` | passed, 4362 jobs | 5.0 s | 5054380 |
| `SMContentCapacity` | passed, 4350 jobs | 7.0 s | 5063288 |
| `SMSignedBalance` including `PatternCountSum` | passed, 4364 jobs | 5.0 s | 5044796 |
| `AuditStructuralExteriorSupport` | passed, 4092 jobs, **102 checks** | 5.5 s | 5176020 |
| `AuditSMStructuralSupport` | passed, 4397 jobs, **202 checks** | 5.3 s | 5390168 |

The **304 strict transitive checks** permit only `propext`, `Classical.choice`
and `Quot.sound`. The existing layer/numerical-evaluator rejection is unchanged.
No new result depends on the external Weyl reduction. The structural line
dimension uses `choose D 0 = choose D D = 1` with D symbolic, not a numerical
rank/multiplicity certificate. SU3/SU2 line triviality uses proved compact
generation and exhaustion.

During development, rewriting h-h inside the full concrete q/l coefficient
type reached the default heartbeat limit. A small abstract indexed-transport
lemma keeps that carrier opaque and closes the original theorem in the final
2.7-second module build. Other development fixes concerned explicit source
finite-dimensional instances, current tensor induction notation and group
map proofs. No resource or Lean proof option was increased.

## Aggregate and repository checks

Aggregate builds also use `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, as in the preceding verified checkpoint.

| Target | Result | Time | Sampled group peak (KiB) |
| --- | --- | --- | --- |
| `Math` | passed, 6030 jobs | 6.5 s | 6202808 |
| `Physics` | passed, 5053 jobs | 5.5 s | 5546968 |

The known GUT root aggregate memory failure recorded in
[the previous verification](joint-branching-verification.md) is unchanged.
It is not a successful full `lake build`; this pass does not repeat that
unchanged failed root build or raise its budget. The final no-build graph
check below records the actual stale frontier.

Repository checks after the result, assumptions, dossier and coverage edits:

- `node tools/layout/check-layout.mjs`: 1717 modules, layers/local imports/
  cycles/aggregate coverage/relocation checks passed.
- `python3 tools/exact-rank/check-retired-certificates.py`: all 19 snapshot
  hashes match, 15 retired modules absent and active imports clean.
- `node tools/docs/check-links.mjs`: 885 Markdown files, 5499 local links,
  110 heading fragments, zero errors.
- All eight new theorem sources contain no `sorry`, custom axiom,
  `native_decide`, `implemented_by` or raised proof limit. Final successful
  focused/aggregate logs have zero warnings and errors. `git diff --check`
  passed; final staged diff and cache checks are recorded below.

The original full q/l support classification remains open at the documented
[general positive-branching interface](structural-classification-boundary.md).

The final `lake --no-build build Math Physics` naming the two structural audit
roots passed with all targets up to date (6634 jobs). The default
`lake --no-build build` returned 3, with exactly `GUT` stale in the 7085-job
graph. This confirms the known root frontier, not a full-build pass.
Statement/assumption/source review, local-link checks, `git diff --check` and
the final staged diff check passed before committing this verified partial
classification milestone. Root README, CSV data, retired archives, toolchain
and dependency pins are unchanged. No merge or push is made.
