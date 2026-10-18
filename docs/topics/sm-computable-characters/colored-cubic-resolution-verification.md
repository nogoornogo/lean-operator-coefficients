# Resolved cubic branching verification

Branch `proof/sm-computable-characters`, base `checkpoint 01`, integration target
`master`. No merge or push. See [results](colored-cubic-resolution-results.md)
and the [bounded helper/source plan](colored-middle-plan.md).

## Guard and trust boundary

Use serialized one-thread `tools/exact-rank/kernel-probe.py` builds, with
6 GiB sampled process-group RSS cap for focused builds, 10 GiB for aggregates,
a 4 GiB host available-memory reserve and 300-second wall-clock cap.
Aggregate/full commands also use `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`. Lean limits and dependency pins are unchanged.

The persistent structural audits retain their layer/original-module checks,
numerical-evaluator rejection lists and three-axiom transitive allowlist:
`propext`, `Classical.choice`, `Quot.sound`. Classical choice selects an
equivalence from the proved finite-length cancellation theorem; no new
existence, branching or irreducibility premise is introduced.

## Focused proof checks

Command form:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- `Math.LinearAlgebra.SymmetricCubeHook` and its representation wrapper:
  passed, including naturality; combined checked run 12.0 s, peak
  4,376,056 KiB.
- `Math.RepresentationTheory.Decomposition.FiniteSummandCancellation`:
  passed, including both directions of the module dictionary, product
  transport and finite length from complex dimension. Initial unused-binder
  warnings were corrected and the dependency was rebuilt below.
- `Math.RepresentationTheory.DoubletCubicHook`: passed, 6.8 s,
  peak 4,775,336 KiB.
- `Math.RepresentationTheory.Decomposition.TensorProductSums`: passed
  as a checked dependency of the full hook split.
- `Math.RepresentationTheory.ExteriorCubeDoubletHook`: passed, 8.3 s,
  peak 4,813,420 KiB. Source comparison, finite common summand and the
  cancellation conclusion are all proved. Explicit carrier parameters
  resolved an initial default-heartbeat failure without raising any limit.
- `Math.RepresentationTheory.SU3DoubleSpinCubeResolved`: passed, 8.3 s,
  peak 4,881,012 KiB, including both color conventions and degree nine.
- `Physics.StandardModel.Operators.SMQResolvedCubeBranching`: passed,
  10.3 s, peak 5,080,676 KiB, for actual signed core species 0 and 5.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`:
  passed, 583 strict transitive checks, 7.0 s, peak 5,289,008 KiB.

Universal permutation/quotient identities normalize at degree three;
no content rank, large invariant multiplicity, character coefficient table
or retired numerical certificate is evaluated. No resource guard triggered
in the successful checks.

## Final acceptance

- Physics structural audit: passed, 296 strict transitive checks, 7.3 s,
  peak 5,433,768 KiB. Together with the Math audit, 879 checks passed.
- Guarded `lake build Math`: passed, 6096 jobs, 8.5 s,
  peak 6,234,788 KiB.
- Guarded `lake build Physics`: passed, 5130 jobs, 7.5 s,
  peak 5,587,100 KiB.
- Guarded default `lake build`: passed, 7166 jobs, 8.3 s,
  peak 6,606,456 KiB; `GUT` rebuilt in 3.7 s. No guard triggered.
- Final successful focused/audit/aggregate/full logs: zero warnings/errors.
- `node tools/layout/check-layout.mjs`: 1790 modules, passed.
- `node tools/docs/check-links.mjs`: 909 Markdown files, 5639 local links
  and 110 fragments checked with zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot
  hashes intact, 15 retired modules absent, active imports clean.
- Eight new Lean modules: forbidden proof/debug tokens and raised proof
  limits absent. Root README, dependency pins and retired sources unchanged.
- Final unstaged/staged diff checks: passed.

Disposable monitored build logs and runner stay under `/tmp`. Reusable
verification is in the source-controlled strict audits; no rank table,
generated numerical certificate or build artifact is added.

## Exact remaining boundary

All six actual Q/conjugate-Q cubic components and their degree-nine duals
are resolved. Quartic-through-sextic Young source identities and the
semantic positive coupling rule for arbitrary restricted color summands
remain unproved. No full mixed q/l support completion is claimed.
