# Joint lepton foundation verification

Continuation from `checkpoint 01` on `proof/sm-computable-characters`; no merge,
push, dependency-pin change or new external premise. The
[result](lepton-joint-results.md) distinguishes complete joint L support
from the unproved general colored/mixed q/l endpoint.

## Proof and audit checks

Final source/audit builds are serialized with one Lean thread, a 6 GiB sampled
process-group RSS cap, 4 GiB available-memory reserve and 300-second guard:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/joint-check.log
```

| Final focused check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| `Math.RepresentationTheory.SU2PairGenerationBounds` | 4057 jobs, pass | — | 5012132 |
| `Physics.StandardModel.Operators.SMLeptonCoreBranching` | 4368 jobs, pass | 26.3 s | 5102136 |
| `Math.RepresentationTheory.SU3ColorPair` (including trace split) | 3874 jobs, pass | 4.3 s | 4782824 |
| `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport` | 4106 jobs, 184 strict checks, pass | 4.5 s | 5236876 |
| `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport` | 4408 jobs, 220 strict checks, pass | 108.7 s | 5402888 |
| `Math` aggregate | 6041 jobs, pass | 6.0 s | 6209056 |
| `Physics` aggregate | 5063 jobs, pass | 202.1 s | 5670944 |

The final Math audit includes the corrected `SU3DefiningExterior` build.
Both persistent audits preserve their layer/original-module and numerical
evaluator/certificate import rejection; 404 strict transitive checks allow
only `propext`, `Classical.choice` and `Quot.sound`. No success is obtained
by a new axiom, an allowlist exception, numerical output or a literature input.

The initial combined arithmetic call in `triple_bounds` reached the unchanged
guard at 21.3 s and 6303184 KiB. It was replaced by small parity-transport
lemmas and separate inequality proofs. The theorem statement and the guard
were unchanged. The subsequent successful focused bounds check is the one
listed above. No large representation basis, character recurrence, rank
numeral or retired certificate was expanded. Intermediate elaboration errors
and unused-simp warnings were corrected before final checks; no Lean proof
limit was increased.

## Aggregate and repository checks

The aggregate invocations additionally set `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, preserving the same guard. Final successful
focused, audit and aggregate logs have no warning or error.

- `lake --no-build build Math Physics Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport`:
  exit 0, all targets up to date, 6647 jobs.
- Default `lake --no-build build`: exit 3, 7098-job graph, exactly `GUT`
  out of date. Its known unchanged aggregate resource boundary is not retried
  as a full compilation; this is not a full default build pass.
- `node tools/layout/check-layout.mjs`: 1730 modules; all layout/layer/import/
  cycle/aggregate/relocation checks pass.
- `node tools/docs/check-links.mjs`: 891 Markdown files, 5538 local links,
  110 heading fragments, zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 hashes match,
  15 retired modules absent, active imports clean.
- All ten new theorem sources contain no `sorry`, custom `axiom`,
  `native_decide`, `implemented_by` or raised heartbeat/recursion setting.
- `git diff --check` and staged diff checks pass. Root README, dependency
  pins, retired sources and numeric CSV outputs are unchanged.
