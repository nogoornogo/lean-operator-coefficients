# Quartic two-component verification

Branch `proof/sm-computable-characters`, resume base `checkpoint 01`, integration
target `master`; no merge or push. See [plan](colored-quartic-plan.md) and
[proved result](colored-quartic-two-results.md).

## Trust and resources

Serialized one-thread builds use `tools/exact-rank/kernel-probe.py` with
a 6 GiB sampled process-group RSS cap for focused checks, 10 GiB for
aggregates/full build, a 4 GiB host reserve and a 300-second wall-clock cap.
Aggregate commands also set
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`.
No Lean proof limit or dependency pin is changed.

The persistent structural audit adds 115 declarations from eight new
modules. Its numerical-evaluator import exclusions, layer/original-module
checks and strict transitive allowlist remain unchanged: only `propext`,
`Classical.choice` and `Quot.sound` are permitted.

The operator identities quantify over arbitrary A vectors. The only
coordinate normalization is for the fixed two-dimensional doublet and
four-slot permutations; no SM content, color basis, rank, exact
multiplicity or character coefficient is enumerated. Their resulting
left inverses and cross exclusions are proved in Lean.

Additive-group instance mismatches in tensor carriers were corrected with
explicit compatible instances. Large inferred kernel carriers were given
explicit parameters and small application lemmas instead of increasing
heartbeat/recursion limits. The linear top-column kernel has explicit
projected insertions and inverse contractions. The retained representation
identification uses the already proved finite-summand cancellation theorem
on two actual completed equivariant splits. It supplies no branching or
irreducibility premise. Initial failed elaborations are not counted as
verified results.

## Focused checks

Command form:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- `Math.LinearAlgebra.AlternatingFour`: passed, 7.8 s, observed process
  group peak 4,326,252 KiB.
- `Math.LinearAlgebra.ExteriorFourthShuffle`: passed as a checked and
  subsequently rebuilt dependency of the two insertion modules.
- `Math.LinearAlgebra.ExteriorFourthDoublet`: passed, including its
  complete contraction/insertion identity and K211 left inverse.
- `Math.LinearAlgebra.ExteriorFourthDoublet22`: passed, including its
  complete identity and K22 left inverse. A successful combined rebuild
  took 29.6 s, peak 5,046,764 KiB.
- `Math.LinearAlgebra.ExteriorFourthDoubletCross`: passed, including
  both vanishing cross contractions and the column exclusions.
- `Math.LinearAlgebra.ExteriorFourthDoubletNaturality`: passed,
  9.3 s, peak 4,841,376 KiB.
- `Math.LinearAlgebra.ExteriorFourthDoubletCauchy`: passed as a rebuilt
  dependency, including injection, symbolic exhaustion and explicit
  projected-kernel inverse identities.
- `Math.RepresentationTheory.ExteriorFourthDoubletCauchy`: final
  successful rebuild 6.2 s within the audit run below; the main equivalence
  and retained-kernel identification both passed.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`:
  passed, 821 strict transitive checks, 11.3 s, observed group peak
  5,323,104 KiB. No guard triggered and no warnings/errors remained.

## Aggregate and repository checks

- Guarded `lake build Math`: passed, 6116 jobs, 5.5 s, observed process
  group peak 6,245,044 KiB.
- Guarded `lake build Physics`: passed from its unchanged proof cache,
  5130 jobs, 3.3 s, observed group peak 862,324 KiB. Its 296 strict
  structural checks were replayed. Together with Math, 1117 pass.
- Guarded default `lake build`: passed, 7186 jobs, 7.3 s, observed group
  peak 6,617,332 KiB; `GUT` rebuilt in 3.1 s. No guard triggered.
- Final audit/aggregate/full-build logs contain zero warnings or errors.
- `node tools/layout/check-layout.mjs`: passed, 1810 modules.
- `node tools/docs/check-links.mjs`: 917 Markdown files, 5688 local
  inline links, 111 fragments, zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot
  hashes intact, 15 retired modules absent, active imports clean.
- Eight new Lean modules: forbidden proof/debug tokens and raised proof
  limits absent. Root README, dependency pins and retired sources unchanged.
- Final unstaged/staged diff checks: passed.

Disposable logs and the guarded full-build runner stay under `/tmp`;
reusable proof and audit code is source-controlled.

## Scope

The generic full-action three-component quartic doublet decomposition and
the actual top-column kernel identification are proved. This does not yet
resolve K211(color tensor weak) or K22(color tensor weak) into the retained
Q color/weak components, supply their general positive color coupling
rule, or complete the original full mixed q/l support classification.
