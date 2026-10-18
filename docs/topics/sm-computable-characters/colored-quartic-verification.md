# Quartic source checkpoint verification

Branch `proof/sm-computable-characters`, base `checkpoint 01`, integration target
`master`. No merge or push. See [plan](colored-quartic-plan.md) and
[results](colored-quartic-results.md). The full quartic endpoint remains open.

## Trust and resources

Serialized one-thread builds use `tools/exact-rank/kernel-probe.py`:
6 GiB sampled process-group RSS cap for focused checks, 10 GiB for
aggregates/full build, a 4 GiB host available-memory reserve and a
300-second wall-clock cap. Aggregate commands also set
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`.
No dependency pin or Lean proof limit changed.

The persistent structural audit was extended by 91 declarations. Its
numerical-evaluator import exclusions, layer/original-module checks and
strict transitive axiom allowlist remain unchanged. The only permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`.

The proofs use a symbolic four-slot alternator, symmetric descent and
arbitrary-dimension polynomial identities. They do not enumerate SM
contents, character coefficients, ranks or representation multiplicities.
An initial default-heartbeat timeout in automated polynomial search was
removed by giving an explicit rational linear combination of the
universal binomial identities; no limit was raised. Tensor carrier
additive-group instance mismatches were corrected before final builds.

## Focused checks

Command form:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- `Math.LinearAlgebra.SectionKernel`: passed, 3.0 s, observed group
  peak 2,730,132 KiB.
- `Math.RepresentationTheory.ExteriorFourthKernels`: passed, including
  the linear construction, 15.3 s, peak 4,396,156 KiB.
- `Math.LinearAlgebra.TensorFourthMultilinear`: passed, 5.3 s,
  peak 4,279,100 KiB.
- `Math.RepresentationTheory.ExteriorFourthColumn`: passed, including
  the linear retraction, 11.0 s, peak 4,398,772 KiB.
- `Math.LinearAlgebra.ExteriorFourthDimensions`: passed as a rebuilt
  dependency in the final audit, including the candidate dimension and
  injectivity-to-exhaustion interface.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`:
  passed, 706 strict transitive checks, 7.8 s, peak 5,310,204 KiB.

## Aggregate and full checks

- Guarded `lake build Math`: passed, 6108 jobs, 6.3 s, observed group
  peak 6,239,624 KiB.
- Guarded `lake build Physics`: passed from its unchanged proof cache,
  5130 jobs, 3.3 s, observed group peak 860,480 KiB. Its 296 strict
  structural checks were replayed. With Math, 1002 structural checks pass.
- Guarded default `lake build`: passed, 7178 jobs, 6.5 s, observed
  group peak 6,612,284 KiB; `GUT` rebuilt in 3.0 s. No guard triggered.
- Final focused/audit/aggregate/full logs contain zero warnings or errors.

- `node tools/layout/check-layout.mjs`: passed, 1802 modules.
- `node tools/docs/check-links.mjs`: 915 Markdown files, 5671 local inline
  links, 111 fragments, zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot
  hashes intact, 15 retired modules absent, active imports clean.
- Seven new Lean modules: forbidden proof/debug tokens and raised proof
  limits absent. Root README, dependency pins and retired sources unchanged.
- Final unstaged/staged `git diff --check`: passed.

Disposable logs and the guarded default-build runner stay under `/tmp`;
the reusable strict audit extension is source-controlled.

## Scope

Actual kernel maps, their two auxiliary equivariant splits, the split top
quartic column and symbolic dimension balance are proved. The other two
quartic component embeddings, their joint independence and retained
color/weak resolution remain unproved. Equal dimensions and an unspecified
remaining kernel are not reported as a full Q quartic classification.
