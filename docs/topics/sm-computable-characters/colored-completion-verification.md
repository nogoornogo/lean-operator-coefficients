# Consecutive colored continuation verification

From `checkpoint 01` on `proof/sm-computable-characters`, targeting `master` with
no merge/push authorization. See [results](colored-completion-results.md)
and the precise [remaining boundary](colored-completion-boundary.md).
Neither general colored endpoint is marked complete.

## Focused proof checks

Serialized one-thread builds use the existing `kernel-probe.py` runner:
6 GiB sampled process-group RSS cap, 4 GiB host available-memory reserve,
300-second timeout, unchanged Lean proof limits and dependency pins.

| Check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| `Math.RepresentationTheory.SymmetricSquareCauchy` (including the linear inverse construction) | pass | 15.8 s | 4373804 |
| `Math.RepresentationTheory.ExteriorSquareTriple` | 3176 jobs, pass | 5.8 s | 4304696 |
| `Math.RepresentationTheory.SU3DoubleSpinSquare` | 3979 jobs, pass | 7.0 s | 4846632 |
| `Math.RepresentationTheory.SU3DoubleSpinExterior` | 3981 jobs, pass | 5.3 s | 4856936 |
| `Physics.StandardModel.Operators.SMQCoreBranching` | 4329 jobs, pass | 7.0 s | 5080532 |
| `Math.RepresentationTheory.SU3TensorTriality` | 3807 jobs, pass | 4.5 s | 4793936 |
| `Math.RepresentationTheory.SU3ColorTensorWord` | 3808 jobs, pass | 4.5 s | 4765888 |
| `Math.RepresentationTheory.TraceFreePairing` | 2993 jobs, pass | 4.0 s | 4106888 |
| `Math.RepresentationTheory.SU3ColorPositive` (including generalized coefficient-product helper) | 3895 jobs, pass | 7.5 s | 4783536 |
| `Math.RepresentationTheory.ExternalCoefficientSupport` | 1723 jobs, pass | 3.0 s | 3180172 |
| `Math.RepresentationTheory.SU3CompatibleCoupling` (including recompiled tensor-positive/triality/word modules) | 4038 jobs, pass | 11.3 s | 4865964 |
| `Physics.StandardModel.Operators.SMQPairHiggsSupport` | 4374 jobs, pass | 5.5 s | 5092876 |
| Math structural audit | 4149 jobs, 472 strict checks, pass | 4.8 s | 5267840 |
| Physics structural audit | 4452 jobs, 288 strict checks, pass | 5.5 s | 5434828 |

All listed final focused builds have no warnings/errors. Instance/unification
heartbeats encountered during development were resolved with explicit
carrier types, reducible local group instances, smaller typed compositions
and an additive-monoid coefficient API. No proof-limit increase, matrix
expansion or numerical content certificate was used. No guard interrupted
the listed checks.

The two persistent structural audits total **760 strict transitive checks**,
allowing only `propext`, `Classical.choice` and `Quot.sound`. They retain
their original axiom allowlists,
layer/origin checks and numerical-import rejections. No desired branching,
positive coupling, irreducibility or literature formula is an extra premise.

## Final aggregate and repository checks

| Check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| Math aggregate | 6076 jobs, pass | 6.5 s | 6222232 |
| Physics aggregate | 5105 jobs, pass | 5.8 s | 5567924 |
| Default full `lake build` | 7144 jobs, pass; GUT rebuilt | 6.3 s | 6591476 |

Aggregates/full builds additionally use `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, with the established 10 GiB sampled RSS
guard, 4 GiB host reserve and 300-second timeout. The exact default command
is `lake build`, monitored by a temporary runner reusing the existing
`kernel-probe.py` RSS/reserve/signal helpers. GUT rebuilt in 2.9 seconds.
No warning/error, memory interruption or raised proof limit occurred.
No Lean source changed after these successful audit/aggregate/full checks.

- Layout: 1776 modules; layers, local imports, cycles, aggregate coverage
  and relocation audits pass.
- Links: 904 Markdown files, 5613 local inline links, 110 fragments, zero errors.
- Retired-certificate check: 19 snapshot hashes match, 15 retired modules
  absent, active imports clean. No retired numerical proof was rebuilt.
- Fifteen new Lean modules contain no forbidden proof/debug/limit directives.
  Root README, numerical CSVs and dependency pins remain unchanged.
- `git diff --check` and final staged diff review pass.

This verifies the bounded consecutive results. Complete higher Q branching
and the general semantic positive-coupling rule for restricted color
summands remain open; no additional assumption closes those interfaces.
