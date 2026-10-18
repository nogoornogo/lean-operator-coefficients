# Middle-cube verification

Continuation from `checkpoint 01` on `proof/sm-computable-characters`. The
[result](colored-cube-results.md) closes actual U/D and conjugate core
middle exterior cubes, not the full original mixed q/l endpoint. No merge,
push, pin/proof-limit change, new external premise or numerical content
rank/multiplicity certificate.

## Focused proof checks

Serialized with one Lean thread, a 6 GiB sampled process-group RSS guard,
4 GiB host available-memory reserve and 300-second timeout:

```sh
env LEAN_NUM_THREADS=1 python3 tools/exact-rank/kernel-probe.py --build --rss-limit-gib 6 --min-available-gib 4 MODULE /tmp/colored-cube-check.log
```

| Check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| `Math.RepresentationTheory.ExteriorCubeHook` | 3177 jobs, pass | 4.5 s | 4303472 |
| `Math.LinearAlgebra.AlternatingThree` | pass | 4.8 s | 4280952 |
| `Math.LinearAlgebra.TensorCubeMultilinear` | 3136 jobs, pass | 4.3 s | 4251936 |
| `Math.LinearAlgebra.ExteriorCubeDoublet` | 3838 jobs, pass | 8.0 s | 4828892 |
| `Math.LinearAlgebra.ExteriorCubeDoubletNaturality` | 3840 jobs, pass | 8.3 s | 4802492 |
| `Math.RepresentationTheory.ExteriorCubeDoublet` (including complete linear split) | 3858 jobs, pass | 10.3 s | 4822612 |
| `Math.RepresentationTheory.SU3SpinExteriorCube` (including hook/trace identification) | 3997 jobs, pass | 9.8 s | 4849472 |
| `Math.RepresentationTheory.SU3ConjugateSpinExteriorCube` (including dual-color hook/trace identification) | 3998 jobs, pass | 11.8 s | 4859208 |
| `Physics.StandardModel.Operators.SMColoredCubeBranching` | 4337 jobs, pass | 4.8 s | 5018288 |
| Math structural audit | 4134 jobs, 353 strict checks, pass | 5.5 s | 5270236 |
| Physics structural audit | 4444 jobs, 267 strict checks, pass | 5.3 s | 5416804 |

The two persistent structural audits total **620 strict transitive checks**.
They allow only `propext`, `Classical.choice` and `Quot.sound`. Their layer,
original-module and numerical-import rejection is unchanged. The audited
actual cube equivalences include both inverse directions. No desired Hom,
branching formula, positivity or adjoint irreducibility is a new premise.

All final successful focused logs have no warnings/errors. Intermediate
elaboration errors, a temporary trace and unused simp arguments were fixed
without changing the frozen target, dependencies or proof limits.
The two-slot spin basis and universal three-slot permutations normalize
maps. Full content exterior bases and coefficient matrices are not expanded.
Completeness uses standard functor dimension identities on the small core,
after constructing and separating its embeddings; it is not a numerical
content rank/multiplicity proof.

## Aggregate and repository checks

| Check | Result | Elapsed | Sampled peak KiB |
| --- | --- | --- | --- |
| Math aggregate | 6063 jobs, pass | 6.8 s | 6219512 |
| Physics aggregate | 5097 jobs, pass | 5.5 s | 5570976 |
| Default full `lake build` | 7129 jobs, pass; GUT rebuilt | 6.5 s | 6590996 |

Aggregate/full builds additionally use `MIMALLOC_PURGE_DELAY=0` and
`MIMALLOC_ARENA_EAGER_COMMIT=0`, with the established 10 GiB sampled RSS
guard, 4 GiB host reserve and 300-second timeout. The default command is
`lake build`, monitored by a temporary runner reusing the existing
`kernel-probe.py` RSS, reserve and signal helpers. GUT actually rebuilt in
2.0 seconds. No warning/error or resource-guard interruption occurred.

- Layout: 1761 modules; layers, local imports, cycles, aggregate coverage
  and relocation audits pass.
- Links: 900 Markdown files, 5597 local inline links, 110 fragments, no errors.
- Retired-certificate checker: 19 snapshot hashes match, 15 retired modules
  absent, active imports clean; no retired certificate was rebuilt.
- Thirteen new Lean modules contain no forbidden proof/debug directives,
  custom axioms or raised proof limits. Numerical CSVs, dependency pins
  and root README are unchanged.
- `git diff --check` and staged diff review pass.

No Lean source changed after the successful audit/aggregate/full checks.
This verifies the bounded cube construction and its actual signed-core
consumers; it does not close the Q-core or general mixed color coupling
interfaces required by the original full q/l endpoint.
