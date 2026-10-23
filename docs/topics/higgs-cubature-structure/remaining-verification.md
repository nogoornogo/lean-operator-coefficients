# Remaining-Family Verification

The [frozen resumed plan](remaining-plan.md) is complete. Both remaining structural
proofs, exact compatibility and all recorded acceptance gates pass.
The earlier [pilot comparison](verification.md) is retained for its own checkpoint.

## Baseline Provenance

All 70 retained transverse/second-collinear entry files match the source hashes
frozen before the rewrite. Their 82-module local dependency closure has retained
actual successful compiler invocations in the completed full-project memory
audit. The selected source/setup/dependency fingerprints, source snapshots,
artifact hashes, compiler logs and matching fresh-compile events were rechecked.
No `Replayed` output is interpreted as a new compilation.

The [baseline summary](remaining-baseline-summary.json) and
[baseline measurements](remaining-before-measurements.csv) report 1,547.397 seconds
for that closure (1,460.427 seconds for the 70 entry files), with maxima of
3.72 GiB resident and 12.35 GiB virtual space. These are historical measurements
of exactly the matching sources, not a new simultaneous baseline run. The
candidate was freshly measured under the same pinned protocol; comparisons
across these recorded runs remain observational.

## Finite-Data Diagnostics And Repair

Exact candidate diagnostics find all six coordinate swaps and a Hadamard
reindexing for the 288-node transverse family. Phase-covariant Gram identities
hold with a common square-one sign. The second-collinear family is exactly the
first-collinear family after exchanging wave labels 2 and 3 and involutively
reindexing the 72 nodes; no additional phase is needed.

The first monolithic transverse certificate prototype reached the unchanged
200,000-heartbeat default in its combined swap and Gram checks (88.46 seconds,
about 4.04 GiB resident). Checks were split by coordinate swap, wave label
and Gram component into small declarations. The split prototype passes in
113.835 seconds, with about 2.97 GiB resident and 8.23 GiB virtual space. No heartbeat, recursion, memory or
time limit is increased. Those certificates concern node identities, not the
old full fourth-moment calculations.


The transverse tensor symmetry, Gram normalization and second-collinear transfer
prototypes all pass with default proof limits. Both complete identities are
unconditional Lean theorems. The producer reproduces the exact candidate data
and split certificate statements; layout and all ten producers (149 outputs)
pass before the final build sequence.


## Consumer And Audit Checkpoint

The 97 affected modules pass serial, dependency-ordered ordinary builds, with
no timeout. The original foundation audit passes with 788 declarations under
its Math-only namespace scope. A new owner-wide strict audit checks all 280
structural declarations, including private helpers, with the same three
standard allowed axioms and Math layer restrictions. The unchanged original
Higgs completeness audit also passes.

The public API check retains 1,677 deprecated import facades and 12,989 aliases.
Reference checks preserve sets and occurrence order in 2,540 canonical modules
outside 606 exact proof fragments (186 parent replacements and all 420 moment
entries). Original statements are compared. The Math namespace check covers
1,996 modules and the unchanged 4,227 historical correspondences. Fresh measurements, all-family type observations and final inventory
reconciliation also pass.


## Reproduction

The retained baseline is selected and verified without compiling or modifying
its old artifact directory:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/lean-memory/compare-higgs-remaining.py \
  --before .lake/proof-memory-audit/fresh-all --baseline-only \
  --output-dir docs/topics/higgs-cubature-structure
```

For a fresh candidate, build the new modules' Lake setup files first. Then use
an empty isolated directory and the same 70 requested entry modules:

```bash
args=()
for family in 0 2; do
  mapfile -t files < <(rg --files Math/Algebra/HiggsFourWaveCubature |
    rg "/R${family}M[0-9]+\.lean$" | sort)
  for file in "${files[@]}"; do
    module="${file%.lean}"
    args+=(--only "${module//\//.}")
  done
done
PYTHONDONTWRITEBYTECODE=1 python3 tools/lean-memory/profile-project.py \
  --work-dir .lake/higgs-cubature-structure/remaining/fresh-candidate "${args[@]}"
PYTHONDONTWRITEBYTECODE=1 python3 tools/lean-memory/compare-higgs-remaining.py \
  --before .lake/proof-memory-audit/fresh-all \
  --after .lake/higgs-cubature-structure/remaining/fresh-candidate \
  --output-dir docs/topics/higgs-cubature-structure
```

The historical full-project snapshot must be available to reproduce that exact
baseline. Otherwise run the frozen pre-rewrite sources into a new isolated
baseline first and identify it as a new measurement. The tools recheck source,
setup, artifact, actual-import and dependency fingerprints; they do not weaken
the full-project profiler/exporter's complete-coverage requirement. Normal local
build artifacts are excluded from the fresh candidate. External pinned package
and toolchain artifacts are reused. Full disposable logs and compiler outputs
remain under ignored build directories.

## Fresh Candidate And Comparison

All 92 selected candidate source/dependency fingerprints compile successfully
in an empty isolated artifact directory: 92 fresh compiler events, zero reused
project artifacts, failures, blocked modules, timeouts or review-threshold
exceedances. The comparison includes all ten added dependencies, including the
first-collinear structural proof compiled afresh. Its actual checked import
graph confirms that neither new structural proof depends on any old fixed-wave
moment module. The old forwarding entry modules are consumers of these proofs.

| Selected closure | Retained before run | Fresh after run |
| --- | ---: | ---: |
| Modules | 82 | 92 |
| Recorded successful compiler invocations | 82 | 92 |
| Total compiler time | 1,547.397 s | 327.052 s |
| Time in 70 entry files | 1,460.427 s | 90.955 s |
| Maximum resident memory | 3.72 GiB | 3.72 GiB |
| Maximum sampled virtual space | 12.35 GiB | 11.28 GiB |

The observed total compiler-time reduction is 78.9%, including the new structural
dependencies. The resident peak remains in unchanged `Basic`. The transverse
node checks themselves use 106.990 seconds and about 2.98 GiB resident in the
fresh run. The [summary](remaining-measurement-summary.json) and
[after measurements](remaining-after-measurements.csv) retain exact source
hashes and run-specific dependency fingerprints. RSS is the OS `wait4` maximum;
virtual space is sampled Linux `VmPeak`, not physical RAM. The pinned external
packages/toolchain are reused. These are cross-run observations, not universal
memory/time bounds or a fresh rebuild of unrelated project sources.

The final ordinary `lake build` passes all 9,735 jobs. All 420 elaborated entry
types are exactly equal before/after, and the original pilot's 140 types also
match its own retained observation. The
[per-name type fingerprints](remaining-theorem-type-checks.json) record that
check. Final constant-inventory reconciliation passes.


## Final Inventory And Acceptance

The current complete exporter observes 72,127 repository constants. Across both
phases, exactly 4,200 old finite-moment compiler helpers are removed and 231
public-namespace structural declarations/auxiliaries are added: the original
Math-only foundation inventory changes from 4,757 to 788. The remaining phase
accounts for 2,800 of those removed helpers. Every old source-declared parent
and protected API remains present. The [exact inventory record](audit-inventory-repairs.json)
checks removed/added name hashes, owners and both disjoint source manifests.
Its other nine count messages are unchanged. Six later Physics extensions of
the Math object namespace are absent from that Math-only audit environment;
they remain unchanged in the global export. All 422 original audit-count records
pass, with the four original parent helper reconciliations and the updated
structural source-extension reconciliation. No Lean audit predicate, layer gate
or axiom allowlist changes.

Final layout checks cover 4,238 modules. All ten source producers reproduce 149
canonical outputs exactly. Exact replay preserves all 4,218 older source paths
outside reviewed proof fragments, plus twelve checksum-guarded structural source
additions. API/reference/namespace checks, profiler controls, negative controls
for proof/inventory boundaries, documentation links, topic navigation, portable
metadata and diff checks pass. New structural sources have no warnings;
existing legacy-import, module-system and retained-binder warnings remain.

The original formulas and theorem hypotheses agree with the Higgs dossier and
assumptions boundary. Literature roles are unchanged and no new bibliography
entry, comparison claim or physical applicability expansion is introduced. The
completed endpoint is committed on the recorded bounded child branch. Parent
and master integration, remote push and branch deletion are outside this work.
