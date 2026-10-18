# Restricted trace-free word verification

Branch `proof/sm-computable-characters`, base `checkpoint 01`, integration target
`master`. No merge or push. See [plan](colored-restricted-plan.md) and
[results](colored-restricted-results.md).

## Resources and trust

Serialized one-thread guarded builds use the existing
`tools/exact-rank/kernel-probe.py`: 6 GiB sampled process-group RSS cap
for focused checks, 10 GiB for aggregates/full build, 4 GiB host reserve
and 300-second wall-clock cap. Aggregate commands also set
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`. No proof limit or
dependency pin is changed.

The persistent Math structural audit retains its numerical-evaluator
import rejections, layer/original-module checks and transitive allowlist
`propext`, `Classical.choice`, `Quot.sound`. It audits the singleton
coefficient exclusion, normalized triple witness, all-degree induction,
whole/trace-free dual-endomorphism equivalences, arbitrary word reduction
and both directions of the closed rule.

## Focused builds

Command form:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- `Math.RepresentationTheory.TraceFreeCoefficientExclusion`: passed as
  a checked dependency below; generic Schur-line exclusion without adjoint
  irreducibility or trace-form duality.
- `Math.RepresentationTheory.TraceFreeTrilinear`: passed; an initial unused
  section-instance warning was corrected and the dependency rebuilt.
- `Math.RepresentationTheory.SU3TraceFreePowers`: passed, 8.0 s, observed
  group peak 4,876,384 KiB; both actual color orientations and joint labels.
- `Math.RepresentationTheory.TraceFreeDualEnd`: passed, 6.0 s, peak
  4,125,960 KiB; the finite scalar summand is cancelled using the proved
  group-algebra bridge.
- `Math.RepresentationTheory.SU3TraceFreeWord`: passed, 7.3 s, peak
  4,892,412 KiB; arbitrary ordering, both orientations and all leaf counts.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`:
  passed, 615 strict transitive checks, 7.3 s, peak 5,295,096 KiB.

No evaluated rank, multiplicity table, character coefficient, retired
numerical certificate or new external premise is used. Successful final
focused runs did not trigger resource guards.

## Final checks

- Guarded `lake build Math`: passed, 6101 jobs, 9.0 s, observed group
  peak 6,236,048 KiB.
- Guarded `lake build Physics`: passed from its unchanged proof cache,
  5130 jobs, 5.0 s, observed group peak 865,700 KiB. Its 296 strict
  structural checks were replayed. With 615 Math checks, 911 passed.
- Guarded default `lake build`: passed, 7171 jobs, 9.3 s, observed group
  peak 6,607,280 KiB; `GUT` rebuilt in 3.0 s. No guard triggered.
- Final successful focused/audit/aggregate/full logs: zero warnings/errors.
- `node tools/layout/check-layout.mjs`: 1795 modules, passed.
- `node tools/docs/check-links.mjs`: 912 Markdown files, 5652 local links,
  110 fragments, zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot
  hashes intact, 15 retired modules absent, active imports clean.
- Five new Lean modules: forbidden proof/debug tokens and raised proof
  limits absent. Root README, dependency pins and retired sources unchanged.
- Final unstaged/staged diff checks: passed.

Disposable logs and the guarded default-build runner stay under `/tmp`.
The reusable audit extension is source-controlled. No generated rank or
multiplicity table is added.

## Still open

The original full mixed q/l support endpoint remains incomplete. The
quartic source target recorded in the plan is not a theorem; Q degrees
four through six and general mixed restricted-Young color coupling remain
proof obligations. A symmetric/exterior quotient of the whole trace-free
word is not covered by its tensor-word iff.
