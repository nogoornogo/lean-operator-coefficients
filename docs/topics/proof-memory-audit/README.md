# Fresh Compilation And Proof Memory Audit

- ID: `proof-memory-audit`
- Status: completed and verified; integrated through the parent into master
- Working branch: `refactor/proof-memory-audit`
- Integration target: `refactor/source-api-compatibility`
- Parent exception: bounded child of the source-API refactor; later chain integration into master was explicitly authorized
- Authorization: user-directed measurement without inherited project caches and replacement of memory-heavy proofs

## Endpoint And Frozen Scope

Measure every module covered by `GUT.lean` by actually invoking the pinned Lean
compiler on its source, with freshly compiled local dependencies. External
Mathlib/TauCeti/Physlib/toolchain artifacts remain pinned reusable inputs.
Preserve the current public source API, theorem statements/hypotheses, proof
limits, strict axiom allowlists and dependency pins. No `sorry`, new axioms,
trust exceptions or higher memory/timeout limits are permitted.

The earlier 15.98 GiB comparison measured two versions of the **unrepaired**
Fierz proof. It does not measure the checked-in coordinate-based repair.
Measure that repair and its dependency closure first, then the entire source graph.

## Plan And Gates

1. Persist a reproducible per-module compiler profiler with isolated output and
   source/setup snapshots. Exclude the ordinary project's compiled output from
   the import search path and rewrite its setup artifact paths into the isolated
   build. Record source/dependency hashes, actual compiler invocations, exits,
   resident/virtual peaks and explicit fresh/reused/blocked status. Ordinary
   incremental Lake success must not count as fresh source compilation.
2. Compile all registered Math/Physics/GUT sources and root aggregates in dependency
   order. Use one compiler process at a time, `-j2`, the existing 16 GiB virtual
   address-space cap and a 540-second timeout per invocation. Disable core dumps.
   Continue independent modules after a failure and identify blocked dependents.
3. Investigate failures and review peaks at or above 6 GiB resident or 14 GiB
   virtual memory. Use matching import-only controls to separate imported
   environment cost from extra proof/elaboration cost. Keep generated certificate
   families and compatibility facades in coverage.
4. Replace costly expansions with semantic intermediate lemmas, factorizations or
   existing independent results. Split proof obligations where useful. Local
   synchronous elaboration may address scheduling/stack reservation, but must be
   distinguished from a mathematical proof improvement. Aim below the review
   thresholds with a clear reduction for proof-driven hotspots; do not merely
   raise the 16 GiB ceiling. Record irreducible import-only costs separately.
5. Recompile changed sources and their dependents, preserving explicit reuse
   accounting. Accept only when every current source/dependency fingerprint has
   a successful measured compilation, no uninvestigated hotspot remains, and
   strict audits, ordinary `lake build`, compatibility checks, layout, links and
   metadata checks pass. Commit verified milestones and the resulting evidence.

Stop for a scope decision only if a fix requires changing a mathematical premise,
a protected interface, dependency pins, a proof/resource limit or an axiom gate.
Do not turn a large import baseline into an unsupported promise that arbitrary
consumer processes use little memory. No external dependency cold rebuild,
physical/numerical simulation or universal compiler-memory guarantee is claimed.

## Profiler

The [compiler profiler](../../../tools/lean-memory/profile-project.py) writes into
a separate ignored audit directory. Each root-project module is rebuilt from its
source snapshot; package/toolchain artifacts remain reusable inputs. `--resume`
only accepts this audit's fingerprinted output and reports that reuse explicitly.
It is not a fresh build of every selected module on every resumed invocation.
To interrupt a long sweep safely between compiler processes, create
`<audit-directory>/pause-request`; the worker saves a partial result and exits
with status 2. Remove that file before resuming. Partial results are not a
successful whole-project check.

```sh
python3 tools/lean-memory/profile-project.py --work-dir .lake/proof-memory-audit/fresh-all --priority Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoContractionRelations
python3 tools/lean-memory/profile-project.py --work-dir .lake/proof-memory-audit/fresh-all --resume --check
python3 tools/lean-memory/export-measurements.py --work-dir .lake/proof-memory-audit/fresh-all --output-dir docs/topics/proof-memory-audit
PYTHONDONTWRITEBYTECODE=1 python3 tools/lean-memory/test-profile-project.py
```

Use a new empty audit directory for a completely fresh run. Ordinary
`lake build` and `lake --no-cache build` are incremental and do not establish
per-module source-regeneration coverage. Full setup/artifact snapshots use disk
space on the project filesystem; `/tmp` may be a smaller memory-backed mount.
The exporter runs the complete current-fingerprint check before writing a portable
CSV and summary. It rejects partial runs and unresolved review-threshold results.

## Current Verification

[Measured improvements and complete verification](verification.md) record
all 4,226 source compilations at the memory-audit checkpoint, the full build
and compatibility gates. Later structural cubature and model additions have
separate records. [Master integration](../source-api-compatibility/master-integration.md)
records the merged-state checks without claiming a new fresh-project sweep.
The source-level theorem/definition changes in this topic are limited to the
[exact reviewed proof-body replacements](proof-rewrites.json).

## Sources And Records

- [Parent source-API topic](../source-api-compatibility/README.md)
- [Earlier original/renamed proof comparison](../source-api-compatibility/resource-investigation.md)
- [Build conventions](../../architecture/BUILD.md)
- [Module ownership and aggregates](../../architecture/MODULE_LAYOUT.md)

The profiler and measurements are implementation verification, not mathematical
premises or literature comparisons. Build artifacts and full logs stay outside
source control. The [per-module manifest](module-measurements.csv),
[protocol/summary](measurement-summary.json) and
[hotspot comparisons](hotspot-measurements.json) retain the measured results.
