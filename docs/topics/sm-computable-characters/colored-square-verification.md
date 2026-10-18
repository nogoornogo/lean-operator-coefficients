# Colored-square verification

Continuation from `checkpoint 01` on `proof/sm-computable-characters`.
The [result](colored-square-results.md) closes the square construction and
two actual colored mixed contents, not the full original q/l endpoint.
No merge, push, dependency or proof-limit change, new literature premise
or numerical rank/multiplicity proof.

## Proof checks

Focused builds are serialized with one Lean thread, a 6 GiB sampled process
group RSS cap, 4 GiB host available-memory reserve and 300-second guard:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/colored-check.log
```

| Check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| `Math.RepresentationTheory.ExteriorSquareCauchy` (including both new linear-algebra modules) | 3172 jobs, pass | 6.0 s | 4338180 |
| `Math.RepresentationTheory.SU3SpinExterior` | 3972 jobs, pass | 6.0 s | 4870184 |
| `Math.RepresentationTheory.SU3ConjugateSpinExterior` (including dual defining exterior) | 3973 jobs, pass | 8.3 s | 4861548 |
| `Physics.StandardModel.Operators.SMColoredCoreBranching` | 4322 jobs, pass | 5.5 s | 5069240 |
| `Physics.StandardModel.Operators.SMColoredSquarePair` (including generic coupled square pairing) | 4324 jobs, pass | 7.5 s | 5021156 |
| `Physics.StandardModel.Operators.SMColoredPairHiggsSupport` (including generation projection) | 4366 jobs, pass | 6.5 s | 5069160 |
| Math structural audit | 4122 jobs, 246 strict checks, pass | 4.8 s | 5247044 |
| Physics structural audit | 4429 jobs, 265 strict checks, pass | 5.3 s | 5417956 |
| Math aggregate | 6051 jobs, pass | 6.0 s | 6206512 |
| Physics aggregate | 5082 jobs, pass | 5.3 s | 5560568 |
| Default full `lake build` | 7116 jobs, pass; GUT actually rebuilt | 6.5 s | 6582804 |

The two persistent structural audits total **511 strict transitive checks**;
only `propext`, `Classical.choice` and `Quot.sound` are allowed. Their
layer/original-module and numerical-import rejection is unchanged. Final
successful logs have no warnings or errors. Intermediate elaboration errors
and unused simp warnings were corrected without raising proof limits or
changing the desired branching/permission statements.

Aggregate/full checks additionally use `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, the established 10 GiB aggregate guard,
4 GiB host reserve and 300-second timeout. The previous full-build recheck
already superseded the old untested GUT boundary.

## Repository checks

- Layout: 1748 modules; layers, local imports, cycles, aggregate coverage
  and relocation audits pass.
- Retired-certificate checker: 19 snapshot hashes match, 15 retired modules
  absent, active imports clean. No retired certificate was rebuilt.
- Eleven new theorem modules contain no `sorry`, custom `axiom`,
  `native_decide`, `implemented_by`, debugging diagnostics or raised proof
  limits. The scalar constants normalize square maps; they are not rank
  or multiplicity certificates.
- Root README, dependency pins and numerical CSVs unchanged.

- Local links: 897 Markdown files, 5583 inline links, 110 fragments,
  zero errors.
- `git diff --check` and final staged diff checks pass.

The default full command was

```sh
env PYTHONDONTWRITEBYTECODE=1 LEAN_NUM_THREADS=1 MIMALLOC_PURGE_DELAY=0 MIMALLOC_ARENA_EAGER_COMMIT=0 lake build
```

A temporary runner reused the existing diagnostic helper's RSS,
available-memory and signal functions to monitor this exact default
command. Exit 0; no interruption, warnings or errors. `GUT` was rebuilt
in 2.9 seconds; sampled whole-group peak was about 6.28 GiB. No Lean source
changed after these successful audit/aggregate/full builds.

The selected bounded square/conjugate/projection/coupling and two-content
consumer milestone is verified. The parent q/l endpoint remains open at
the named middle-cube, Q-core and general compatible color coupling
interfaces. This checkpoint does not import their desired conclusions or
convert an unevaluated matching test into a completed classification.
