# Cubic bridge and exterior-word verification

Branch `proof/sm-computable-characters`, base `checkpoint 01`, integration target
`master`. No merge or push. The [result](colored-middle-results.md) remains
partial with respect to the original full colored q/l endpoint.

## Resource and trust boundary

Serialized builds use `LEAN_NUM_THREADS=1` and
`tools/exact-rank/kernel-probe.py`, a 4 GiB host available-memory reserve,
300-second timeout, 6 GiB sampled process-group RSS cap for focused modules
and 10 GiB for aggregates/full build. Aggregate commands also use
`MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0`.
Lean proof limits and dependency pins are unchanged.

The persistent structural audits retain the existing layer/original-module
checks and numerical-evaluator import rejections. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted transitively. No evaluated
content rank, multiplicity certificate, new literature premise, custom axiom
or excluded retired numerical module is used by the new results.

## Executed focused checks

Each command has the form

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build \
  --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/LOG
```

- `Math.LinearAlgebra.ExteriorSymmetricColumn`: passed, including naturality.
- `Math.LinearAlgebra.ExteriorCubeDoubletCauchy`: passed; arbitrary-dimension
  column/hook independence, symbolic exhaustion and equivalence.
- `Math.RepresentationTheory.ExteriorCubeDoubletCauchy`: passed.
- `Math.RepresentationTheory.SU3DoubleSpinCube`: passed, including degree nine.
- `Math.RepresentationTheory.SU3ExteriorColorWord`: passed, 5.8 s,
  observed group peak 4,774,216 KiB.
- `Physics.StandardModel.Operators.SMQCubeBranching`: passed, 8.8 s,
  observed group peak 5,046,608 KiB.
- `Math.RepresentationTheory.Audit.AuditStructuralExteriorSupport`: passed,
  513 strict transitive checks, 9.5 s, observed peak 5,270,320 KiB.
- `Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport`: passed,
  292 strict transitive checks, 8.3 s, observed peak 5,421,772 KiB.

Initial elaboration attempts exposed carrier-instance mismatches and default
heartbeat failures. Retaining the original exterior carrier's group
structure, deriving compatible additive groups for auxiliary kernel tensors,
and composing existing intertwining equalities resolved these. No limit was
raised and no proof statement was weakened. The successful runs had no
warnings and did not trigger a guard.

## Aggregate and repository checks

- Guarded `lake build Math`: passed, 6081 jobs, 7.3 s, observed group
  peak 6,225,868 KiB.
- Guarded `lake build Physics`: passed, 5110 jobs, 11.3 s, observed group
  peak 5,572,916 KiB. This also rebuilt the final Physics audit formatting.
- Guarded default `lake build`: passed, 7150 jobs, 12.0 s, observed group
  peak 6,599,400 KiB. `GUT` rebuilt in 3.8 s; the final Math audit and
  aggregate were checked after audit-list formatting. No guard was triggered.
- Both structural audits passed with 513 Math and 292 Physics checks
  (805 total). Their allowlists and import rejection rules are unchanged.
- Successful focused/aggregate/full logs: zero warnings.
- `node tools/layout/check-layout.mjs`: 1782 modules, passed.
- `node tools/docs/check-links.mjs`: 907 Markdown files, 5625 local links,
  110 heading fragments, zero errors.
- `python3 tools/exact-rank/check-retired-certificates.py`: 19 snapshot
  hashes intact, 15 retired modules absent, active imports clean.
- Six new Lean modules: no forbidden proof/debug tokens or raised proof
  limits. `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` unchanged.
- `git diff --check` and final staged diff checks: passed.

Disposable logs and the monitored default-build runner remain under `/tmp`;
no generated rank table or build output is committed. The source-controlled
structural audits cover the new maps, inverse/exhaustion theorems, actual
Q adapters and both directions of the exterior-word rule.

## Remaining theorem obligations

The Q color/weak hook's internal branching, complete degree-four-through-six
Young splittings and the positive coupling rule for arbitrary restricted
Young color summands are not proved. Neither the coarse Q equivalence nor
the exterior-only coupling iff is reported as full endpoint 2 completion.
